(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_123.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_123 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0501c92ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL02BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL05XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL03kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxQR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxS73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_123=LibSegNa_qxSZ3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qxL0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781832].
Definition STOPS1 : list Z := [781832; 781864; 781760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=#3$?$10$11$12$13$14$15+$32#20+$32#30$21$19##7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18!&6+$32#20#3#7???8000,1#3'$21##7???????????!$21#,1$24'$24##??)$21##1$32##40"%pstring).
Definition ss0 : sym_state := SS 781648 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (32), ELit 1)].
Definition F0L : list SR.region := [((EVar 50), (32), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;>>08#;>>28#;>=<0#;>>08#5=#;>>08,20#$1$2$3$4$5$6$7$8$9+$32#20$24#3##3$?$10$11$12$13$14$15+$32#20+$32#30$21$19#1#7???8000$1<$1=$1>$1?,,:!$32#20,1$24'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18!&6+$32#20#3#7???8000,1#3'$21##7???????????!$21#,1$24'$24##??)$21##1$32##40,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781648 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781648 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxL0.

Module LibSegNa_qxL1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781832].
Definition STOPS1 : list Z := [781832; 781864; 781760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=#3$?$10$11$12$13$14$15+$32#20+$32#30$21$19#1#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18!&6+$32#21#3#7???8000,1#3'$21##7???????????!$21#,1$24'$24##??)$21##1$32##40"%pstring).
Definition ss0 : sym_state := SS 781648 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (33), ELit 1)].
Definition F0L : list SR.region := [((EVar 50), (33), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;>>08#;>>28#;>=<0#;>>08#5=#;>>08,20#$1$2$3$4$5$6$7$8$9+$32#21$24#3#1#3$?$10$11$12$13$14$15+$32#20+$32#30$21$19#2#7???8000$1<$1=$1>$1?,,:!$32#21,1$24'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18!&6+$32#21#3#7???8000,1#3'$21##7???????????!$21#,1$24'$24##??)$21##1$32##40,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781648 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781648 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxL1.

Module LibSegNa_qxL2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781760].
Definition STOPS1 : list Z := [781760; 781864; 781832] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=#3$?$10$11$12$13$14$15+$32#20+$32#30$21$19#2#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18!&6+$32#22#3#7???8000,1#3'$21##7???????????!$21#,1$24'$24##??)$21##1$32##40!$32#20,1$25!$32#21,1$26'$25##??'$26##??"%pstring).
Definition ss0 : sym_state := SS 781648 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (34), ELit 1); ((EVar 50), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 50), (34), 1); ((EVar 50), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;>=<0#;>>28#;>>08#;>=<0#5=#;>=<0,20#$1$2$3$4$5$6$7$8$9&9$24#3?&8&6$24#6&6@^#1#$26#3:&6$24#6#2#3$?$10$11$12$13$14$15+$32#20+$32#30$21+$32#30#4#7???8000$1<$1=$1>$1?,,12!$32#33,1&9$24#3?!$32#32,1&8&6$24#6&6@^#1#$26#3:!$32#31,1&8&6$26#4&6@^#4#$25#3:!$32#30,1&6$25#2!$32#22,1$24'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18!&6+$32#22#3#7???8000,1#3'$21##7???????????!$21#,1$24'$24##??)$21##1$32##40!$32#20,1$25!$32#21,1$26'$25##??'$26##??,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781760 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781648 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781648 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxL2.

Module LibSegNa_qxQB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 781812] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$22#26613$15$16$17$18+$2;$32$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#33!+$2;$32#,1$2=###7???<<;8#14'$2=##3?!$2=#26613,1$2>'$2>##??"%pstring).
Definition ss0 : sym_state := SS 781760 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?4640#;>=?4#?4640#5=#?4640,20##;>=>4$2$3$4$5$6$7$8$9$22$2>$<$=$>$?$10$11$12$22#26613$15$16$17$18+$2;$32$1:#7???8000$1<$1=$1>$1?,,9'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#33!+$2;$32#,1$2=###7???<<;8#14'$2=##3?!$2=#26613,1$2>'$2>##??,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781760 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781760 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxQB.

Module LibSegNa_qxQE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781832].
Definition STOPS1 : list Z := [781832; 781760] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$2:$16$17$18+$2;$32#1$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488355264;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 64);
   KRange (EVar 43) 48 51;
   KRange (EVar 42) 0 1099511627776].
Definition ss0 : sym_state := SS 781796 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>>08#;>=<0#;>>08#5=#;>>08,20#$1$2$3$4$5$6$7$8$9$:$;$<$=#3$?$10$11$12$13$14+$2:#4$16$17$18++$2;$32#1#$1;$1<$1=$1>$1?,,5'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#33'$2:##10000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781796 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781796 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxQE.

Module LibSegNa_qxQR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781760].
Definition STOPS1 : list Z := [781760; 781824] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18+$2;$32$29$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488355264;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 64);
   KRange (EVar 41) 2 4;
   KRange (EVar 43) 48 51].
Definition ss0 : sym_state := SS 781796 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=<0#;>>00#;>=<0#5=#;>=<0,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18++$2;$32#1+$29-1$1;$1<$1=$1>$1?,,5'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$29#2#4'$2;#30#33,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781760 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781796 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781796 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxQR.

Module LibSegNa_qxS1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 1);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 0].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#1#$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#1'&9$21#7##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS1.

Module LibSegNa_qxS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 2);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 1].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#2&9$21#7$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#2'&9$21#7##1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS2.

Module LibSegNa_qxS3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 3);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 2].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#3&9$21#7$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#3'&9$21#7##2,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS3.

Module LibSegNa_qxS4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 4);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 3].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#4&9$21#7$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#4'&9$21#7##3,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS4.

Module LibSegNa_qxS5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 5);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 4].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#5&9$21#7$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#5'&9$21#7##4,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS5.

Module LibSegNa_qxS6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 6);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 5].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#6&9$21#7$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#6'&9$21#7##5,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS6.

Module LibSegNa_qxS7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KWord (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) 1 (ELit 7);
   KRange (EAlu Instr.ALU_AND (EVar 33) (ELit 7)) 0 6].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#7&9$21#7$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,3'$21##7???????????!&6$21#3#7???8000,1#7'&9$21#7##6,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxS7.

Module LibSegNa_qxSZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781648].
Definition STOPS1 : list Z := [781648; 782344] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; (EVar 33); EVar 25; EVar 26; ELit 2147450880; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 1)].
Definition ss0 : sym_state := SS 781632 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=50#;?008#;>=50#5=#;>=50,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$21$19$1:#7???8000$1<$1=$1>$1?,,2'$21##7???????????#&6$21#3#7???8000#1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781648 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxSZ.

End BndP_Na_123.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_003.
Module BndP_Na_124.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_124 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0501c92ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT02BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT05XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxT03kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT122BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT123NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT122BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT125XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT122F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT123PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT124planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT125regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxT123kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxTB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124>LibSegNa_qxTQR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxV3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_qxVE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124<LibSegNa_qxZ3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_e1e97c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4D3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4E3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4F3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4G3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_124=LibSegNa_rs4L3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qxT0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [782148].
Definition STOPS1 : list Z := [782148; 520280; 781900] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$22#26613$2:+$32#20+$32#30$18$19##7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$2#7???7?8010:0#800000000000&$2#20!$2-90,8$32!$2-98,8$32'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40"%pstring).
Definition ss0 : sym_state := SS 781868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;>?44#7?058#;>>4<#;>?44#5=#;>?44,20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$22#26613$2:$32$32$18$19##7???8000$1<$1=$1>$1?,,7'$2#7???7?8010:0#800000000000&$2#20!$2-90,8$32!$2-98,8$32'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 782148 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxT0.

Module LibSegNa_qxT12.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280; 782140; 781900] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$22#26613$2:+$32#20+$32#30$18$19$29#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488355264;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 64);
   KRange (EVar 41) 1 2].
Definition ss0 : sym_state := SS 781868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#7?058#;>?3<#;>>4<#7?058#5=#7?058,20##;>>4<+$2-:0$3$4$5$6$7$8+$2-:0++$29$32#20#+@-1$29#3$=$>$?$10$11$12$22#26613$2:+$32#20+$32#30$18$19$29#7???8000$1<$1=$1>$1?,,4'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$29#1#2,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 520280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxT12.

Module LibSegNa_qxTB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781976].
Definition STOPS1 : list Z := [781976] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12$22#26613$2:+$32#20+$32#30$18$19$29#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18'$29#1#2!$32#20,1$25!$32#21,1$26!$32#22,1$2<'$25##??'$26##??'$2<##??"%pstring).
Definition ss0 : sym_state := SS 781900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (48), ELit 3)].
Definition F0L : list SR.region := [((EVar 50), (48), 3)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>>98#;>>98#5=#;>>98,20#$1+$2-:0$3$4$5$6$7$8+$2-:0&8&6$2<#6&6@^#1#$26#3:&6@^#1#$26#3:+@#100000000$29#100000000$=$>$?$10$11+$29#1$22#26613$2:+$32#30+$32#30$18$19$29#7???8000$1<$1=$1>$1?,,>!$32#32,1&8&6$2<#6&6@^#1#$26#3:!$32#31,1&8&6$26#4&6@^#4#$25#3:!$32#30,1&6$25#2'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32#20#18'$29#1#2!$32#20,1$25!$32#21,1$26!$32#22,1$2<'$25##??'$26##??'$2<##??,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781976 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxTB.

Module LibSegNa_qxTQB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 782352; 782064] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$22#26613$15+$2;$32+$2;$32$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#32!&6+$2;$32#3#7???8000,1#4'&9+$2;$32#7##2!+$2;$32#,1$2=###7???<<;8#14'$2=##3?!$2=#26613,1$2>'$2>##??"%pstring).
Definition ss0 : sym_state := SS 781976 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#?4640#;?010#;>>?0#?4640#5=#?4640,20##;>><<$2$3$4$5$6$7$8$9$22$2>$<$=$>$?$10$11$12$22#26613$15+$2;$32+$2;$32$18$19$1:#7???8000$1<$1=$1>$1?,,;'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#32!&6+$2;$32#3#7???8000,1#4'&9+$2;$32#7##2!+$2;$32#,1$2=###7???<<;8#14'$2=##3?!$2=#26613,1$2>'$2>##??,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781976 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781976 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxTQB.

Module LibSegNa_qxTQE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [782148].
Definition STOPS1 : list Z := [782148; 782084; 781976] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11#1$13$14$2:+$2;$32+$2;$32$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8010:0#800000000000&$2#20!$2-:0,8#!$2-90,8$32!$2-98,8$32'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#32'$2:##10000000000"%pstring).
Definition ss0 : sym_state := SS 782028 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;>?44#;>?04#;>>98#;>?44#5=#;>?44,20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11#$13$14+$2:#1$32$32$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?8010:0#800000000000&$2#20!$2-:0,8#!$2-90,8$32!$2-98,8$32'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$2;#30#32'$2:##10000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 782148 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 782028 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 782028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxTQE.

Module LibSegNa_qxTQR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781976].
Definition STOPS1 : list Z := [781976; 782076] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$29$13$14$2:+$2;$32+$2;$32$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488355264;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 64);
   KRange (EVar 41) 2 3;
   KRange (EVar 43) 48 50;
   KRange (EVar 42) 0 1099511627776].
Definition ss0 : sym_state := SS 782028 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>>98#;>>?<#;>>98#5=#;>>98,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11+$29-1$13$14+$2:#1++$2;$32#1++$2;$32#1$18$19$1:$1;$1<$1=$1>$1?,,6'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40'$29#2#3'$2;#30#32'$2:##10000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781976 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 782028 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 782028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxTQR.

Module LibSegNa_qxV.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781632].
Definition STOPS1 : list Z := [781632; 781868] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11+$21$23$13$14$15$16$17$21$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327;
   KRange (EVar 35) 2 67108864;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 2 140737488355328].
Definition ss0 : sym_state := SS 781832 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>=40#;>>2<#;>=40#5=#;>=40,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11+$21$23$13$14$15$16$17+$21#1$19$1:$1;$1<$1=$1>$1?,,3'$21##7???????????'$23#2#4000000'+$21$23#2#800000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781632 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781832 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781832 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxV.

Module LibSegNa_qxVE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [781868].
Definition STOPS1 : list Z := [781868; 781632] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11+$21#1$13$14$15$16$17$21$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355327].
Definition ss0 : sym_state := SS 781832 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>>2<#;>=40#;>>2<#5=#;>>2<,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11+$21#1$13$14$15$16$17+$21#1$19$1:$1;$1<$1=$1>$1?,,1'$21##7???????????,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781868 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 781832 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 781832 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxVE.

Module LibSegNa_qxZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0501c9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0501c9.IT.
Definition ENDS : list Z := [782324].
Definition STOPS1 : list Z := [782324; 782228] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$34+$2-:0$:$;$<$=$>$?$10$11$12$13$14$2:$32$32$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?8010:0#800000000000&$2#20!$2-88,8+&6$32#3#7???8000'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32##8(&6$32#3#7???8000#8!$32#38,8$33'$33#1000#7???????????($33##1)##7???7000#100000001000$33##1)$32##40$33##1'$34#7???7?8010:0#800000000000&$34#10!$34-8,8$35!$34-10,8$36!$34-18,8$37!$34-20,8$38!$34-28,8$39!$34-30,8$3:!$34-38,8$3;!$34-40,8$3<!$34-48,8$3=!$34-50,8$3>!$34-58,8$3?!$34-60,8$40!$34-68,8$41)+$34-:0##:0$32##40)+$34-:0##:0$33##1"%pstring).
Definition ss0 : sym_state := SS 782148 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 8); ((EVar 51), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 50), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 8); ((EVar 51), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>??4#;>?94#;>??4#5=#;>??4,20#$35$34$3$4$5$6$7$36$37$2:+&6$32#3#7???8000$<$=$>$?$10$11$38$39$3:$3;$3<$3=$3>$3?$40$41$1<$1=$1>$1?,,27!$33#,1#!&6$32#3#7???8003,1^#?#??????????????5!&6$32#3#7???8002,1^#?#??????????????5!&6$32#3#7???8001,1^#?#??????????????5!&6$32#3#7???8000,1^#?#??????????????5!&6$32#3#7???8007,1^#?#??????????????5!&6$32#3#7???8006,1^#?#??????????????5!&6$32#3#7???8005,1^#?#??????????????5!&6$32#3#7???8004,1^#?#??????????????5!$32#,8#45>0360>'$2#7???7?8010:0#800000000000&$2#20'$32#6;6000#7?????????<0&$32#20)##7???7000#100000001000$32##40($32##8(&6$32#3#7???8000#8!$32#38,8$33'$33#1000#7???????????($33##1)##7???7000#100000001000$33##1)$32##40$33##1'$34#7???7?8010:0#800000000000&$34#10!$34-8,8$35!$34-10,8$36!$34-18,8$37!$34-20,8$38!$34-28,8$39!$34-30,8$3:!$34-38,8$3;!$34-40,8$3<!$34-48,8$3=!$34-50,8$3>!$34-58,8$3?!$34-60,8$40!$34-68,8$41)+$34-:0##:0$32##40)+$34-:0##:0$33##1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 782324 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0501c9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 782148 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0501c9.IT BndT_Na_000.SegItab_Na_0501c9.IT_sound BF NX0 BR XSTEP F0 PSS plan 782148 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qxZ.

Module LibSegNa_rs4D.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e1e97c.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e1e97c.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 44; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$22'&9$22#1#1#1'$22#1;#2=!$:#8,8#"%pstring).
Definition ss0 : sym_state := SS 999896 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##?42=<+$2-50$3$4$5$6$7$:#2?#30$22#1#16$>$?$10$11$12#30#+@#2&6$22#1-1#1+@#2&6$22#1-1$18$19$1:$1;$1<$1=$1>$1?,,17!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$22'&9$22#1#1#1'$22#1;#2=!$:#8,8#,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e1e97c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 999896 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e1e97c.IT BndT_Na_003.SegItab_Na_e1e97c.IT_sound BF NX0 BR XSTEP F0 PSS plan 999896 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_rs4D.

Module LibSegNa_rs4E.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e1e97c.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e1e97c.IT.
Definition ENDS : list Z := [519092].
Definition STOPS1 : list Z := [519092] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:#2?$25$;$<$=$>$?$10$11$39#30#$3:#1$38$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$:#10,8$23'$23#1000#800000000000'$3:##40"%pstring).
Definition ss0 : sym_state := SS 1000156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;4#7>;;4#5=#7>;;4,20##?435<+$2-50$3$4$5$6$7$:#2?$25$23#1$=$>$?$10$11$25$23#$3:#1$38$18$19$1:$1;$1<$1=$1>$1?,,13'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34!$:#10,8$23'$23#1000#800000000000'$3:##40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 519092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e1e97c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1000156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e1e97c.IT BndT_Na_003.SegItab_Na_e1e97c.IT_sound BF NX0 BR XSTEP F0 PSS plan 1000156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_rs4E.

Module LibSegNa_rs4F.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e1e97c.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e1e97c.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:#2?$36$;$<$=$>$?$10$11$25$23#$3:#1$38$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$23#1000#800000000000'$3:##40"%pstring).
Definition ss0 : sym_state := SS 1000284 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?1?<0#?1?<0#5=#?1?<0,20##?438<+$2-50$3$4$5$6$7$:#2?$23+$3:#1$<$=$>$?$10$11$25$23#$3:#1$38$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$23#1000#800000000000'$3:##40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 991168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e1e97c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1000284 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e1e97c.IT BndT_Na_003.SegItab_Na_e1e97c.IT_sound BF NX0 BR XSTEP F0 PSS plan 1000284 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_rs4F.

Module LibSegNa_rs4G.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e1e97c.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e1e97c.IT.
Definition ENDS : list Z := [1000388].
Definition STOPS1 : list Z := [1000388] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$:#2?$36$;$<$=$>$?$10$11$25$23#$3:#1$38$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$25#1000#800000000000'$3:##40"%pstring).
Definition ss0 : sym_state := SS 1000332 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 10), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?43<4#?43<4#5=#?43<4,20#$2<$2$3$4$5$6$7$2=$2>#31$;$<$=$>$?$10$11$2?$30$31$32$33$34$18$19$1:$1;$1<$1=$1>$1?,,15!$:#10,8$25!$:#8,8#!$:#,8#31'$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33!$2-48,8$34'$25#1000#800000000000'$3:##40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1000388 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e1e97c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1000332 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e1e97c.IT BndT_Na_003.SegItab_Na_e1e97c.IT_sound BF NX0 BR XSTEP F0 PSS plan 1000332 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_rs4G.

Module LibSegNa_rs4L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e1e97c.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e1e97c.IT.
Definition ENDS : list Z := [999924].
Definition STOPS1 : list Z := [999924] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; ELit 44; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$22'&9$22#1#1#1'$22#2?#8000001"%pstring).
Definition ss0 : sym_state := SS 999896 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?41?4#?41?4#5=#?41?4,20#$1$2$3$4$5$6$7$8$9$:#2<+@#2&6$22#1-1$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='$2#7???7?800040#800000000000&$2#10($2-50#50'$:#6;6000#7?????????>8&$:#8($:##18)$2-50#50$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$22'&9$22#1#1#1'$22#2?#8000001,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 999924 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e1e97c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 999896 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e1e97c.IT BndT_Na_003.SegItab_Na_e1e97c.IT_sound BF NX0 BR XSTEP F0 PSS plan 999896 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_rs4L.

End BndP_Na_124.
Module BndP_Na_118.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_118 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_14d4782ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA02BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA05XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118>LibSegNa_qvtA03kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk1e13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118ALibSegNa_qvtAk2e13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118=LibSegNa_qvtC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtCqV3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDKz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118@LibSegNa_qvtDV1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_118?LibSegNa_qvtDV23kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qvtA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [412000].
Definition STOPS1 : list Z := [412000; 742224] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487328 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-160)) (ELit 160)].
Definition ss0 : sym_state := SS 742096 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-160), ELit 160)].
Definition F0L : list SR.region := [((EVar 2), (-160), 160)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64960#;5350#64960#5=#64960,20##;5350+$2-:0$3$4$5$6$7$2+$2-:0#60#15?:78#1$=$>$?$10$11$12$13$:$=$16$<$;$19$1:#7???8000$1<$1=$1>$1?,,15!$2-88,8$>!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2-:0,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010:0#800000000000&$2#20($2-:0#:0,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 412000 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742096 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742096 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtA0.

Module LibSegNa_qvtA16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [412000].
Definition STOPS1 : list Z := [412000; 742224] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2#10$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487328 140737488355312;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-160)) (ELit 176)].
Definition ss0 : sym_state := SS 742096 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 160)].
Definition F0L : list SR.region := [((EVar 2), (-144), 160)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64960#;5350#64960#5=#64960,20##;5350+$2-:0$3$4$5$6$7+$2#10+$2-:0#60#15?:78#1$=$>$?$10$11$12$13$:$=$16$<$;$19$1:#7???8000$1<$1=$1>$1?,,15!$2-88,8$>!$2-58,8$1;!$2-50,8$1:!$2-48,8$19!$2-40,8$18!$2-38,8$17!$2-30,8$16!$2-28,8$15!$2-20,8$14!$2-18,8$13!$2-10,8$12!$2-8,8$9!$2#,8$8!$2#8,8$1!$2-90,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010:0#7??????????0&$2#20($2-:0#;0,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 412000 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742096 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742096 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtA16.

Module LibSegNa_qvtAk1e1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [743848].
Definition STOPS1 : list Z := [743848] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$14$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-14,4$2=!$25-10,4#1,$25-8#8'$2=##1($25-8#8)+$25-18##18$24##60"%pstring).
Definition ss0 : sym_state := SS 743728 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 37), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;59:8#;59:8#5=#;59:8,20#$1$2$3$4$5$6$7$8$9+$25-10$2=+&6+$25-10#3#7???8000#1#2+$50#1$10$11$12+$24#50$14$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,11!$25-8,8+$50#1'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-14,4$2=!$25-10,4#1'$2=##1($25-8#8)+$25-18##18$24##60,51!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 743848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743728 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743728 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtAk1e1.

Module LibSegNa_qvtAk2e0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [743848].
Definition STOPS1 : list Z := [743848] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$14$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-14#3#7???8000#1!$25-14,4#2!$25-10,4#($25-10#4)+$25-18##18$24##60"%pstring).
Definition ss0 : sym_state := SS 743728 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (-16), ELit 4)].
Definition F0L : list SR.region := [((EVar 37), (-16), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;59:8#;59:8#5=#;59:8,20#$1$2$3$4$5$6$7$8$9+$25-10#1+&6+$25-10#3#7???8000##2$?$10$11$12+$24#50$14$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,>!$25-10,4#1'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-14#3#7???8000#1!$25-14,4#2($25-10#4)+$25-18##18$24##60,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 743848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743728 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743728 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtAk2e0.

Module LibSegNa_qvtAk2e1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [743848].
Definition STOPS1 : list Z := [743848] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$14$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-14,4#2!$25-10,4#1,$25-8#8($25-10#4($25-8#8)+$25-18##18$24##60"%pstring).
Definition ss0 : sym_state := SS 743728 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (-16), ELit 4); ((EVar 37), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 37), (-16), 4); ((EVar 37), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;59:8#;59:8#5=#;59:8,20#$1$2$3$4$5$6$7$8$9+$25-10#+&6+$25-10#3#7???8000#1#2+$50#1$10$11$12+$24#50$14$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,11!$25-10,4#!$25-8,8+$50#1'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-14,4#2($25-10#4($25-8#8)+$25-18##18$24##60,51!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 743848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743728 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743728 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtAk2e1.

Module LibSegNa_qvtB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [742404].
Definition STOPS1 : list Z := [742404] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$32$;$<$=$>$?$10$11$12$13$24$15$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8010:0#800000000000&$2#20($2-70#8)+$2-:0##:0$32##80'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##18(&6$32#3#7???8000#<'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1)&6+$24#50#3#7???8000#1&6$32#3#7???8000#10)+$2-:0##:0$24##60"%pstring).
Definition ss0 : sym_state := SS 742224 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 8); ((EVar 50), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-112), 8); ((EVar 50), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;5404#;5404#5=#;5404,20#$1+$2-:0$3$4$5$6$7$8+$2-:0##1518:#;52=0^#?#??????????????2^#?#??????????????8^#?#??????????????1$10$11$32+$24#50$24$15+&6+$24#50#3#7???8000$17$18+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?,,1?!$2-70,8$32!&6$32#3#7???800;,1^#?#??????????????3!&6$32#3#7???800:,1^#?#??????????????3!&6$32#3#7???8009,1^#?#??????????????8!&6$32#3#7???8008,1^#?#??????????????8!&6$32#3#7???8003,1^#?#??????????????1!&6$32#3#7???8002,1^#?#??????????????1!&6$32#3#7???8001,1^#?#??????????????1!&6$32#3#7???8000,1^#?#??????????????1!&6$32#3#7???8007,1^#?#??????????????2!&6$32#3#7???8006,1^#?#??????????????2!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8!$32#10,8#;52=0!$32#8,8#1518:!$32#,8#41;58:;3'$2#7???7?8010:0#800000000000&$2#20($2-70#8)+$2-:0##:0$32##80'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##18(&6$32#3#7???8000#<'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1)&6+$24#50#3#7???8000#1&6$32#3#7???8000#10)+$2-:0##:0$24##60,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 742404 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742224 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742224 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtB.

Module LibSegNa_qvtC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 743728] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14+$24#30$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 743716 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?4640#;5930#?4640#5=#?4640,20##;5930$2$3$4$5$6$7$8$9+$24#30#3:$<$=$>$?$10$11$12$13$14+$24#30$16$17$18$19$1:$1;$1<$1=$1>$1?,,,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743716 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743716 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtC.

Module LibSegNa_qvtCqK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 743716] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14+$24#30$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 743704 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?4640#;5924#?4640#5=#?4640,20##;5924$2$3$4$5$6$7$8$9+$24#30#22$<$=$>$?$10$11$12$13$14+$24#30$16$17$18$19$1:$1;$1<$1=$1>$1?,,,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743704 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtCqK.

Module LibSegNa_qvtCqV.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 743728] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14+$24#30$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 743408 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?4640#;5930#?4640#5=#?4640,20##;5930$2$3$4$5$6$7$8$9+$24#30#22$<$=$>$?$10$11$12$13$14+$24#30$16$17$18$19$1:$1;$1<$1=$1>$1?,,,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743408 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743408 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtCqV.

Module LibSegNa_qvtDKn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 742956] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-10,4#!$25-8,8$2;'$2;#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?4640#;562<#?4640#5=#?4640,20##;562<$2$3$4$5$6$7$8$9+$24#30#2<$25#$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,?'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-10,4#!$25-8,8$2;'$2;#1^#?#???????????????,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDKn.

Module LibSegNa_qvtDKz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [742956].
Definition STOPS1 : list Z := [742956] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-10,4#!$25-8,8#"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;562<#;562<#5=#;562<,20#$1$2$3$4$5$6$7$8$9##$25#$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,>'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-10,4#!$25-8,8#,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 742956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDKz.

Module LibSegNa_qvtDV1n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [1001024; 742856] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8$2;'$2;#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?4640#;55<8#?4640#5=#?4640,20##;55<8$2$3$4$5$6$7$8$9+$24#30#2<$25#$>$?$10$11$12+$24#50$24+$24#30+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8$2;'$2;#1^#?#???????????????,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1001024 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDV1n.

Module LibSegNa_qvtDV1z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [742856].
Definition STOPS1 : list Z := [742856] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8#"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;55<8#;55<8#5=#;55<8,20#$1$2$3$4$5$6$7$8$9##$25#$>$?$10$11$12+$24#50$24+$24#30+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,10'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-14#3#7???8000#1#&6+$25-8#3#7???8000#1!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8#,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 742856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDV1z.

Module LibSegNa_qvtDV2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [742856].
Definition STOPS1 : list Z := [742856] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-14#3#7???8000#1!$25-18,4#1!$25-14,4#2!$25-10,4#1"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;55<8#;55<8#5=#;55<8,20#$1$2$3$4$5$6$7$8$9#2#2$25#$>$?$10$11$12+$24#50$24+$24#30+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,>'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1#&6+$25-14#3#7???8000#1!$25-18,4#1!$25-14,4#2!$25-10,4#1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 742856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDV2.

End BndP_Na_118.
Module BndP_Na_119.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_119 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_14d4782ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtDa3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_30a3b92ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119?LibSegNa_qvtDb23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKLS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIKSS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVLS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtIVSS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119>LibSegNa_qvtJ13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKdS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_119@LibSegNa_qvtKe0L3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qvtDa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [743036].
Definition STOPS1 : list Z := [743036] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1#&6+$24#10#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1!$25-18,4#!$25-10,4#1!$24#10,8$26'$26#6;6000#7??????????8"%pstring).
Definition ss0 : sym_state := SS 742404 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;567<#;567<#5=#;567<,20#$1$2$3$4$5$6$7$8$9$26#$25#$>$?$10$11$12+$24#50$24$15+&6+$24#50#3#7???8000$17$18$19$1:#7???8000$1<$1=$1>$1?,,?'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1#&6+$24#10#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1!$25-18,4#!$25-10,4#1!$24#10,8$26'$26#6;6000#7??????????8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 743036 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742404 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742404 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDa.

Module LibSegNa_qvtDb2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_30a3b9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_30a3b9.IT.
Definition ENDS : list Z := [801916].
Definition STOPS1 : list Z := [801916; 743160] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$26$;$<$=$>$?$10$11$12$13$14$23$16$22$21+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<%#10000#158000'$26#6;6000#7?????????<8)##7???7000#100000001000$26##38#&6$26#3#7???8000#1!$26#,8#151130)$32##80$26##38)&6$26#3#7???8000#1&6$32#3#7???8000#10###80022236#1)##80021074#1&6$32#3#7???8000#10'$21#6;6000#7??????????0)##7???7000#100000001000$21##10#&6$21#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#,8$30!$21#8,8$31'$30##800000000000'$31##4000000)&6$21#3#7???8000#1&6$32#3#7???8000#10)&6+$21#8#3#7???8000#1&6$32#3#7???8000#10'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32#20#10(&6$32#3#7???8004#2'$2#7???7?8010:0#800000000000&$2#20!$2-88,8$3<)+$2-:0##:0$32##80"%pstring).
Definition ss0 : sym_state := SS 743036 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (32), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (32), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<3<7<#;56?8#<3<7<#5=#<3<7<,20##;56?8+$2-:0$3$4$5$6$7$8+$2-:0$26+$32#20$22$23$3<#<3<7<$10$11$12$13$14$23$16$22$21+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?,,1>!$32#28,8$31!$32#20,8$30!&6$32#3#7???8005,1#!&6$32#3#7???8004,1#%#10000#158000'$26#6;6000#7?????????<8)##7???7000#100000001000$26##38#&6$26#3#7???8000#1!$26#,8#151130)$32##80$26##38)&6$26#3#7???8000#1&6$32#3#7???8000#10###80022236#1)##80021074#1&6$32#3#7???8000#10'$21#6;6000#7??????????0)##7???7000#100000001000$21##10#&6$21#3#7???8000#1#&6+$21#8#3#7???8000#1'$30##800000000000'$31##4000000)&6$21#3#7???8000#1&6$32#3#7???8000#10)&6+$21#8#3#7???8000#1&6$32#3#7???8000#10'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32#20#10(&6$32#3#7???8004#2'$2#7???7?8010:0#800000000000&$2#20!$2-88,8$3<)+$2-:0##:0$32##80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 801916 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_30a3b9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743036 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_30a3b9.IT BndT_Na_000.SegItab_Na_30a3b9.IT_sound BF NX0 BR XSTEP F0 PSS plan 743036 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtDb2.

Module LibSegNa_qvtIKLL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743704] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 742972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;5918#;95?0#5=#;95?0,20##;5918$2$3$4$5$6$7$8$9+$24#30+$2=$2>$2:+$29$2:$29$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,17'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIKLL.

Module LibSegNa_qvtIKLS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743704] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##2<'&9$28#1##"%pstring).
Definition ss0 : sym_state := SS 742972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;5918#;95?0#5=#;95?0,20##;5918$2$3$4$5$6$7$8$9+$24#30+$2=$2>+$24#19++$24&6$28#1#19&6$28#1$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##2<'&9$28#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIKLS.

Module LibSegNa_qvtIKSL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743704] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 742972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;5918#;95?0#5=#;95?0,20##;5918$2$3$4$5$6$7$8$9+$24#30++$24&6$2<#1#31$2:+$29$2:$29$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIKSL.

Module LibSegNa_qvtIKSS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743704] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##2<'&9$28#1##"%pstring).
Definition ss0 : sym_state := SS 742972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;5918#;95?0#5=#;95?0,20##;5918$2$3$4$5$6$7$8$9+$24#30++$24&6$2<#1#31+$24#19++$24&6$28#1#19&6$28#1$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,;'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##2<'&9$28#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIKSS.

Module LibSegNa_qvtIVLL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743408] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 742868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;57?0#;95?0#5=#;95?0,20##;57?0$2$3$4$5$6$7$8$9+$24#30+$2=$2>$2:+$29$2:$29$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,17'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIVLL.

Module LibSegNa_qvtIVLS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743408] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##2<'&9$28#1##"%pstring).
Definition ss0 : sym_state := SS 742868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;57?0#;95?0#5=#;95?0,20##;57?0$2$3$4$5$6$7$8$9+$24#30+$2=$2>+$24#19++$24&6$28#1#19&6$28#1$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#40#3#7???8000#1#&6+$24#38#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##??'&9$2<#1#1#1!$24#38,8$2='$2=##80000000!$24#40,8$2>'$2>#1000#800000000000!$24#18,1$28'$28##2<'&9$28#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIVLS.

Module LibSegNa_qvtIVSL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743408] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 742868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;57?0#;95?0#5=#;95?0,20##;57?0$2$3$4$5$6$7$8$9+$24#30++$24&6$2<#1#31$2:+$29$2:$29$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,11'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIVSL.

Module LibSegNa_qvtIVSS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [759280].
Definition STOPS1 : list Z := [759280; 743408] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##2<'&9$28#1##"%pstring).
Definition ss0 : sym_state := SS 742868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;95?0#;57?0#;95?0#5=#;95?0,20##;57?0$2$3$4$5$6$7$8$9+$24#30++$24&6$2<#1#31+$24#19++$24&6$28#1#19&6$28#1$?$10$11$12$13$24+$24#30$16$17$18$19$1:#7???8000$1<$1=$1>$1?,,;'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#30#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#30,1$2<'$2<##2<'&9$2<#1##!$24#18,1$28'$28##2<'&9$28#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 759280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtIVSS.

Module LibSegNa_qvtJ1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [743728].
Definition STOPS1 : list Z := [743728] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18+&6$32#3#7???8000$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 50) 7036928 140737488355200;
   KAlign (EVar 50) 32;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 50) 0) (ELit 128);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) 2147450884) (ELit 2)].
Definition ss0 : sym_state := SS 743160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), ELit 2)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;5930#;5930#5=#;5930,20#$1$2$3$4$5$6$7$8$9^#?#??????????????8$;$<$=$>$?$10$11$12$13$14$15$16$17$18+&6$32#3#7???8000$1:$1;$1<$1=$1>$1?,,6!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80(&6$32#3#7???8004#2,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 743728 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 743160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 743160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtJ1.

Module LibSegNa_qvtKdL2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_30a3b9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_30a3b9.IT.
Definition ENDS : list Z := [798520].
Definition STOPS1 : list Z := [798520; 743624] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+$24#50$24$23+&6+$24#50#3#7???8000$17$18+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2<%#10000#158000'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1#&6+$24#10#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1!$25-18,4#!$25-10,4#!$24#10,8$26'$26#6;6000#7?????????<8)##7???7000#100000001000$26##38#&6$26#3#7???8000#1!$26#,8#151130###80022232#1)$32##80$26##38)&6$26#3#7???8000#1&6$32#3#7???8000#10)##80021070#1&6$32#3#7???8000#10!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32#40#10(&6$32#3#7???8008#2)$32##80$24##60)&6$24#3#7???8000#<&6$32#3#7???8000#10'$2#7???7?8010:0#800000000000&$2#20!$2-88,8$3<)+$2-:0##:0$32##80"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (64), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (8), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (64), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (8), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<2?38#;58<8#<2?38#5=#<2?38,20##;58<8+$2-:0$3$4$5$6$7$8+$2-:0$26+$32#40$23$3<#<2?38$?$10$11$12+$24#50$2:$23+&6+$24#50#3#7???8000$17$18+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?,,2<!$32#48,8$29!$32#40,8$2:!&6$32#3#7???8009,1#!&6$32#3#7???8008,1#%#10000#158000'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1#&6+$24#10#3#7???8000#1#&6+$24#18#3#7???8000#1#&6+$24#28#3#7???8000#1#&6+$24#20#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18!$24#10,8$26'$26#6;6000#7?????????<8)##7???7000#100000001000$26##38#&6$26#3#7???8000#1!$26#,8#151130###80022232#1)$32##80$26##38)&6$26#3#7???8000#1&6$32#3#7???8000#10)##80021070#1&6$32#3#7???8000#10!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32#40#10(&6$32#3#7???8008#2)$32##80$24##60)&6$24#3#7???8000#<&6$32#3#7???8000#10'$2#7???7?8010:0#800000000000&$2#20!$2-88,8$3<)+$2-:0##:0$32##80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 798520 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_30a3b9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_30a3b9.IT BndT_Na_000.SegItab_Na_30a3b9.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtKdL2.

Module LibSegNa_qvtKdS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_30a3b9.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_30a3b9.IT.
Definition ENDS : list Z := [798520].
Definition STOPS1 : list Z := [798520; 743624] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+$24#50$24$23+&6+$24#50#3#7???8000$17$18+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26%#10000#158000'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1#&6+$24#10#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1#&6+$25-18#3#7???8000#1!$25-18,4#!$25-10,4#!$24#10,8$26'$26#6;6000#7?????????<8)##7???7000#100000001000$26##38#&6$26#3#7???8000#1!$26#,8#151130###80022232#1)$32##80$26##38)&6$26#3#7???8000#1&6$32#3#7???8000#10)##80021070#1&6$32#3#7???8000#10!$24#18,1$28'$28##2<'&9$28#1##'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32#40#10(&6$32#3#7???8008#2)$32##80$24##60)&6$24#3#7???8000#<&6$32#3#7???8000#10'$2#7???7?8010:0#800000000000&$2#20!$2-88,8$3<)+$2-:0##:0$32##80"%pstring).
Definition ss0 : sym_state := SS 742708 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (64), ELit 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (8), ELit 2)].
Definition F0L : list SR.region := [((EVar 50), (64), 16); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (8), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<2?38#;58<8#<2?38#5=#<2?38,20##;58<8+$2-:0$3$4$5$6$7$8+$2-:0$26+$32#40$23$3<#<2?38$?$10$11$12+$24#50+$24#19$23+&6+$24#50#3#7???8000$17$18+&6$32#3#7???8000$32#7???8000$1<$1=$1>$1?,,26!$32#48,8&6$28#1!$32#40,8+$24#19!&6$32#3#7???8009,1#!&6$32#3#7???8008,1#%#10000#158000'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#50#3#7???8000#1#&6+$24#10#3#7???8000#1#&6+$24#18#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18!$24#10,8$26'$26#6;6000#7?????????<8)##7???7000#100000001000$26##38#&6$26#3#7???8000#1!$26#,8#151130###80022232#1)$32##80$26##38)&6$26#3#7???8000#1&6$32#3#7???8000#10)##80021070#1&6$32#3#7???8000#10!$24#18,1$28'$28##2<'&9$28#1##'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32#40#10(&6$32#3#7???8008#2)$32##80$24##60)&6$24#3#7???8000#<&6$32#3#7???8000#10'$2#7???7?8010:0#800000000000&$2#20!$2-88,8$3<)+$2-:0##:0$32##80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 798520 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_30a3b9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742708 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_30a3b9.IT BndT_Na_000.SegItab_Na_30a3b9.IT_sound BF NX0 BR XSTEP F0 PSS plan 742708 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtKdS2.

Module LibSegNa_qvtKe0L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_14d478.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_14d478.IT.
Definition ENDS : list Z := [781284].
Definition STOPS1 : list Z := [781284; 742708] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+$24#50$24$15$16#$21$19$1:#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#18#3#7???8000#1#&6+$24#20#3#7???8000#1#&6+$24#28#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1!$25-10,4#!$24#18,1$28'$28##??'&9$28#1#1#1!$24#20,8$29'$29##80000000!$24#28,8$2:'$2:#1000#800000000000($24#20#8($2:##1)##7???7000#100000001000$2:##1#&6$2:#3#7???8000#1)$2:##1$24##60)$2:##1+$25-18##18'$21#6;6000#7??????????0)##7???7000#100000001000$21##10#&6$21#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#,8$30!$21#8,8$31'$30##800000000000'$31##4000000)$21##10$24##60)$21##10$2:##1"%pstring).
Definition ss0 : sym_state := SS 742404 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (32), ELit 8); ((EVar 42), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (32), 8); ((EVar 42), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;>;>4#;5534#;>;>4#5=#;>;>4,20##;5534$2$3$4$5$6$7$8$9$30+$30$31#26613+$24#18$>$?$10$11$12+$24#50$24$15$16#$21$19$1:#7???8000$1<$1=$1>$1?,,22!$24#20,8#!$2:#,1#'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6+$24#18#3#7???8000#1#&6+$24#20#3#7???8000#1#&6+$24#28#3#7???8000#1!$24#50,8$25'$25#1018#800000000000&$25#8)##7???7000#100000001000+$25-18##18#&6+$25-10#3#7???8000#1!$24#18,1$28'$28##??'&9$28#1#1#1'$29##80000000!$24#28,8$2:'$2:#1000#800000000000($24#20#8($2:##1)##7???7000#100000001000$2:##1)$2:##1$24##60)$2:##1+$25-18##18'$21#6;6000#7??????????0)##7???7000#100000001000$21##10#&6$21#3#7???8000#1#&6+$21#8#3#7???8000#1!$21#,8$30!$21#8,8$31'$30##800000000000'$31##4000000)$21##10$24##60)$21##10$2:##1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 781284 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_14d478.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 742404 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_14d478.IT BndT_Na_000.SegItab_Na_14d478.IT_sound BF NX0 BR XSTEP F0 PSS plan 742404 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvtKe0L.

End BndP_Na_119.
Module BndP_Na_045.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_045 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0e2eda2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS22BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS25XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS23kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS92BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS92BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS95XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS94planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azlS93kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_d4be312ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrE33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_045>LibSegNa_azrF23kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_azlS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#60!$21#10,8+$24#60'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#8$21#<0#100#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#60+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#60!$21#10,8+$24#60'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS2.

Module LibSegNa_azlS3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#<0!$21#10,8+$24#<0'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#10$21#180#200#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#<0+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#<0!$21#10,8+$24#<0'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS3.

Module LibSegNa_azlS4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#180!$21#10,8+$24#180'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#20$21#300#400#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#180+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#180!$21#10,8+$24#180'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS4.

Module LibSegNa_azlS5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#300!$21#10,8+$24#300'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#40$21#600#800#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#300+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#300!$21#10,8+$24#300'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS5.

Module LibSegNa_azlS6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#600!$21#10,8+$24#600'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#80$21#<00#1000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#600+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#600!$21#10,8+$24#600'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS6.

Module LibSegNa_azlS7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#<00!$21#10,8+$24#<00'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#100$21#1800#2000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#<00+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#<00!$21#10,8+$24#<00'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS7.

Module LibSegNa_azlS8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#1800!$21#10,8+$24#1800'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#200$21#3000#4000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#1800+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#1800!$21#10,8+$24#1800'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS8.

Module LibSegNa_azlS9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#3000!$21#10,8+$24#3000'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#400$21#6000#8000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#3000+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#3000!$21#10,8+$24#3000'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS9.

Module LibSegNa_azrE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d4be31.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d4be31.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#"%pstring).
Definition ss0 : sym_state := SS 848248 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##<?:54+$2-80$3$4$5$6$7#1$23#18#20#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$21$22#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$2-80,8+$21#8!$2-78,8#<?2>8!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d4be31.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 848248 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d4be31.IT BndT_Na_003.SegItab_Na_d4be31.IT_sound BF NX0 BR XSTEP F0 PSS plan 848248 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azrE0.

Module LibSegNa_azrE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d4be31.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d4be31.IT.
Definition ENDS : list Z := [519100].
Definition STOPS1 : list Z := [519100] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7#1$23$28$;$<$=$>$?$10$11$21$22#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",35'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-80,8+$21#8!$2-78,8#<?2>8!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 850516 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 40), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 40), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;<#7>;;<#5=#7>;;<,20##<?82<+$2-:0$3$4$5$6$7+$2-68$21$28###7???8000$>$?$10$11$28#7???8000#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,41!$2-;0,8+$2-68!$2-:8,8#<?7=8!$2-98,8$22!$2-90,8$21!$2-88,8$23!$2-80,8+$21#8!$2-78,8#<?394!$2-58,8+$28#18!$28#10,8#!$28#8,8$27!$28#,4$26!$2-50,8+$28#18!$2-60,8$28!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 519100 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d4be31.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 850516 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d4be31.IT BndT_Na_003.SegItab_Na_d4be31.IT_sound BF NX0 BR XSTEP F0 PSS plan 850516 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azrE1.

Module LibSegNa_azrE2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d4be31.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d4be31.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8#!$21#8,8#!$21#10,8#'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#<?394!$2-80,8+$21#8!$2-88,8$23!$2-90,8$21!$2-98,8$22!$2-68,8$28!$2-60,8$28!$2-58,8+$28#18!$2-50,8+$28#18!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 849964 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##<?:=4+$2-80$3$4$5$6$7+$21#8$23$28+$28#18+$28#18+$28#18&6+$21#10#3$?$10$11$21$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2=!$2-80,8+$21#8!$2-78,8#<?394!$2-68,8#!$2-50,8#!$21#10,8+$28#18!$2-58,8#!$21#8,8+$28#18!$2-60,8#!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$23!$2-90,8$21!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d4be31.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 849964 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d4be31.IT BndT_Na_003.SegItab_Na_d4be31.IT_sound BF NX0 BR XSTEP F0 PSS plan 849964 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azrE2.

Module LibSegNa_azrE3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d4be31.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d4be31.IT.
Definition ENDS : list Z := [848860].
Definition STOPS1 : list Z := [848860] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$23$:$;$<$=$>$?$10$11$21$22#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$28!$21#8,8+$28#18!$21#10,8+$28#18'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#<?394!$2-80,8+$21#8!$2-68,8#!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 850644 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?3=<#<?3=<#5=#<?3=<,20#$2;$2$3$4$5$6$7$2<$2=$28###7???8000#+&6+$2-58#3#7???8000$10$11$2>$2?$30$31$32$17$18$19$1:$1;$1<$1=$1>$1?,,22!$21#8,8+$28#18!$2-78,8#<?3:8'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$28!$21#10,8+$28#18'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-80,8+$21#8!$2-68,8#!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 848860 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d4be31.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 850644 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d4be31.IT BndT_Na_003.SegItab_Na_d4be31.IT_sound BF NX0 BR XSTEP F0 PSS plan 850644 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azrE3.

Module LibSegNa_azrF1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d4be31.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d4be31.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>8&$24#10'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000"%pstring).
Definition ss0 : sym_state := SS 848248 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##<?774+$2-80$3$4$5$6$7+$21#8$23$24$29+$24$25++$24$25#18$24$29$10$11$21$22+$24$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,20!$2-80,8+$21#8!$2-78,8#<?1?4!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>8&$24#10'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d4be31.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 848248 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d4be31.IT BndT_Na_003.SegItab_Na_d4be31.IT_sound BF NX0 BR XSTEP F0 PSS plan 848248 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azrF1.

Module LibSegNa_azrF2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d4be31.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d4be31.IT.
Definition ENDS : list Z := [848860].
Definition STOPS1 : list Z := [848860] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$23$:$;$<$=$>$?$10$11$21$22+$24$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3:'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>8&$24#10'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#<?1?4!$2-80,8+$21#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000#&6+$24$25#3#7???8000#3(+$24$25##18)##7???7000#100000001000+$24$25##18)##10000#6:6000+$24$25##18'+$24$25#1000#7?????????>8)$2-1000#1000+$24$25##18)$21##18+$24$25##18)$22##4+$24$25##18)$23##4+$24$25##18"%pstring).
Definition ss0 : sym_state := SS 849780 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), ELit 24); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), 24); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?3=<#<?3=<#5=#<?3=<,20#$2;$2$3$4$5$6$7$2<$2=+$24$25##$=$>$?$10$11$2>$2?$30$31$32$17$18$19$1:$1;$1<$1=$1>$1?,,3=!$21#8,8++$24$25#18!+$24$25#10,8#!+$24$25#8,8$27!+$24$25#,4$26'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#10,8$29'$24#1000#7?????????>8&$24#10'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#<?1?4!$2-80,8+$21#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000#&6+$24$25#3#7???8000#3(+$24$25##18)##7???7000#100000001000+$24$25##18)##10000#6:6000+$24$25##18'+$24$25#1000#7?????????>8)$2-1000#1000+$24$25##18)$21##18+$24$25##18)$22##4+$24$25##18)$23##4+$24$25##18,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 848860 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d4be31.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 849780 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d4be31.IT BndT_Na_003.SegItab_Na_d4be31.IT_sound BF NX0 BR XSTEP F0 PSS plan 849780 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azrF2.

End BndP_Na_045.
Module BndP_Na_043.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_043 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_2d87ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS62BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS65XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS63kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS92BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS92BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS95XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS94planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azeS93kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0e2eda2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlE33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlF23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043=LibSegNa_azlH3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_043>LibSegNa_azlI13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_azeS6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_2d87ed.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_2d87ed.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#600!$21#10,8+$24#600'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 810932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##<68<<+$2-80$3$4$5$6$7#80$21#<00#1000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#600+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#<6124!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#600!$21#10,8+$24#600'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_2d87ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 810932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_2d87ed.IT BndT_Na_000.SegItab_Na_2d87ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 810932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azeS6.

Module LibSegNa_azeS7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_2d87ed.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_2d87ed.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#<00!$21#10,8+$24#<00'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 810932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##<68<<+$2-80$3$4$5$6$7#100$21#1800#2000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#<00+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#<6124!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#<00!$21#10,8+$24#<00'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_2d87ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 810932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_2d87ed.IT BndT_Na_000.SegItab_Na_2d87ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 810932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azeS7.

Module LibSegNa_azeS8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_2d87ed.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_2d87ed.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#1800!$21#10,8+$24#1800'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 810932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##<68<<+$2-80$3$4$5$6$7#200$21#3000#4000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#1800+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#<6124!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#1800!$21#10,8+$24#1800'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_2d87ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 810932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_2d87ed.IT BndT_Na_000.SegItab_Na_2d87ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 810932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azeS8.

Module LibSegNa_azeS9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_2d87ed.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_2d87ed.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#3000!$21#10,8+$24#3000'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 810932 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##<68<<+$2-80$3$4$5$6$7#400$21#6000#8000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#3000+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#<6124!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#3000!$21#10,8+$24#3000'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_2d87ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 810932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_2d87ed.IT BndT_Na_000.SegItab_Na_2d87ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 810932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azeS9.

Module LibSegNa_azlE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#1$21#18#20#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlE0.

Module LibSegNa_azlE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [519100].
Definition STOPS1 : list Z := [519100] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7#1$21$28$;$<$=$>$?$10$11$23$22#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",36'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3#&6+$28#4#3#7???8000#1($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 40), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 40), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;<#7>;;<#5=#7>;;<,20##;89=4+$2-:0$3$4$5$6$7+$2-68$21$28###7???8000$>$?$10$11$28#7???8000#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,43!$2-;0,8+$2-68!$2-:8,8#;8980!$2-98,8$22!$2-90,8$23!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;8744!$2-58,8+$28#18!$28#10,8#!$28#8,4&4#+$27-2!$28#4,4$27!$28#,4$26!$2-50,8+$28#18!$2-60,8$28!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8#!$21#8,8#!$21#10,8#'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3#&6+$28#4#3#7???8000#1($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 519100 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756916 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlE1.

Module LibSegNa_azlE2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8#!$21#8,8#!$21#10,8#'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8$28!$2-58,8+$28#18!$2-50,8+$28#18!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#18+$28#18+$28#18&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2=!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8#!$2-50,8#!$21#10,8+$28#18!$2-58,8#!$21#8,8+$28#18!$2-60,8#!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$28#1000#7?????????>8&$28#10)##7???7000#100000001000$28##18#&6$28#3#7???8000#3($28##18)$2-1000#1000$28##18)$21##18$28##18)##10000#6:6000$28##18)$22##4$28##18)$23##4$28##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlE2.

Module LibSegNa_azlE3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [755596].
Definition STOPS1 : list Z := [755596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$21$:$;$<$=$>$?$10$11$23$22#+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$28!$21#8,8+$28#18!$21#10,8+$28#18'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-68,8#!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 757100 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;878<#;878<#5=#;878<,20#$2;$2$3$4$5$6$7$2<$2=$28###7???8000#+&6+$2-58#3#7???8000$10$11$2>$2?$30$31$32$17$18$19$1:$1;$1<$1=$1>$1?,,22!$21#8,8+$28#18!$2-78,8#;8758'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$28!$21#10,8+$28#18'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-80,8+$21#8!$2-68,8#!$2-60,8#!$2-58,8#!$2-50,8#!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 755596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757100 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 757100 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlE3.

Module LibSegNa_azlF1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>8&$24#10'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;891<+$2-80$3$4$5$6$7+$21#8$21$24$29+$24$25++$24$25#18$24$29$10$11$23$22+$24$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,20!$2-80,8+$21#8!$2-78,8#;8564!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>8&$24#10'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlF1.

Module LibSegNa_azlF2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [755596].
Definition STOPS1 : list Z := [755596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$21$:$;$<$=$>$?$10$11$23$22+$24$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3;'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8$29'$24#1000#7?????????>8&$24#10'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8564!$2-80,8+$21#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000#&6+$24$25#3#7???8000#3#&6++$24$25#4#3#7???8000#1(+$24$25##18)##7???7000#100000001000+$24$25##18)##10000#6:6000+$24$25##18'+$24$25#1000#7?????????>8)$2-1000#1000+$24$25##18)$21##18+$24$25##18)$22##4+$24$25##18)$23##4+$24$25##18"%pstring).
Definition ss0 : sym_state := SS 755996 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), ELit 24); ((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 36) (EVar 37)), (0), 24); ((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;878<#;878<#5=#;878<,20#$2;$2$3$4$5$6$7$2<$2=+$24$25##$=$>$?$10$11$2>$2?$30$31$32$17$18$19$1:$1;$1<$1=$1>$1?,,3?!$21#8,8++$24$25#18!+$24$25#10,8#!+$24$25#8,4&4#+$27-2!+$24$25#4,4$27!+$24$25#,4$26'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#10,8$29'$24#1000#7?????????>8&$24#10'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8564!$2-80,8+$21#8'$25##;?>8&$25#8'$29#1018#7???????????'&1$29+$24$25#18#<000#&6+$24$25#3#7???8000#3#&6++$24$25#4#3#7???8000#1(+$24$25##18)##7???7000#100000001000+$24$25##18)##10000#6:6000+$24$25##18'+$24$25#1000#7?????????>8)$2-1000#1000+$24$25##18)$21##18+$24$25##18)$22##4+$24$25##18)$23##4+$24$25##18,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 755596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 755996 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 755996 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlF2.

Module LibSegNa_azlG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$2:$21$28$;$<$=$>$?$10$11$23$22$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",40'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>8&$24#10'$25#18#6000&$25#8'$2:#2#800'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????'$28#1000#7?????????=0&$28#10(+$28$25##18#&6+$28$25#3#7???8000#3#&6++$28$25#4#3#7???8000#1#&6++$25$28#4#3#7???8000#1'+$25$28#1000#7?????????>8&+$25$28#8#&6+$25$28#3#7???8000#3)##7???7000#100000001000+$28$25##18'+$28$25#1000#7?????????>8)$2-1000#1000+$28$25##18)$21##18+$28$25##18)##10000#6:6000+$28$25##18)$22##4+$28$25##18)$23##4+$28$25##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EAlu Instr.ALU_ADD (EVar 40) (EVar 37)), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EAlu Instr.ALU_ADD (EVar 40) (EVar 37)), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8404+$2-;0$3$4$5$6$7+$2-68$21$24+$24$25+$24$25+$24$25&6+$21#8#3$?$10$11$23#7???8000$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,4=!$2-;0,8+$2-68!$2-:8,8#;8980!$2-98,8$22!$2-90,8$23!$2-88,8$21!$2-80,8+$21#8!$2-78,8#;8744!$2-58,8++$25$28#18!+$25$28#10,8#!+$25$28#8,4&4#+$27-2!+$25$28#4,4$27!+$25$28#,4$26!$2-50,8+$28@#18$2:!$2-60,8+$25$28!$2-68,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>8&$24#10'$25#18#6000&$25#8'$2:#2#800'$22#6;6000#7??????????<&$22#4)##7???7000#100000001000$22##4#&6$22#3#7???8000#1!$22#,4$26)$2-1000#1000$22##4)$21##18$22##4'$23#6;6000#7??????????<&$23#4)##7???7000#100000001000$23##4#&6$23#3#7???8000#1!$23#,4$27)$2-1000#1000$23##4)$21##18$23##4'$26##7???????'$27##7???????'$28#1000#7?????????=0&$28#10(+$28$25##18#&6+$28$25#3#7???8000#3#&6++$28$25#4#3#7???8000#1#&6++$25$28#4#3#7???8000#1'+$25$28#1000#7?????????>8&+$25$28#8#&6+$25$28#3#7???8000#3)##7???7000#100000001000+$28$25##18'+$28$25#1000#7?????????>8)$2-1000#1000+$28$25##18)$21##18+$28$25##18)##10000#6:6000+$28$25##18)$22##4+$28$25##18)$23##4+$28$25##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756916 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlG.

Module LibSegNa_azlH.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [519100].
Definition STOPS1 : list Z := [519100] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$12#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",34'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>8&$24#10'$25#18#6000&$25#8'$2:#2#800'$28#1000#7?????????=0&$28#10(+$28$25##18#&6+$28$25#3#7???8000#3)##7???7000#100000001000+$28$25##18'+$28$25#1000#7?????????>8)$2-1000#1000+$28$25##18)$21##18+$28$25##18)##10000#6:6000+$28$25##18)$22##4+$28$25##18)$23##4+$28$25##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28$25!$2-58,8++$28$25#18!$2-50,8+$28@#18$2:!$2-48,8$21!$2-:8,8#;8980!$2-;0,8+$2-68"%pstring).
Definition ss0 : sym_state := SS 754692 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;<#7>;;<#5=#7>;;<,20##;89=4+$2-:0$3$4$5$6$7+$2-68$21$28$24$25$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,34'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24$25!$21#10,8+$24$25'$24#1000#7?????????>8&$24#10'$25#18#6000&$25#8'$2:#2#800'$28#1000#7?????????=0&$28#10(+$28$25##18#&6+$28$25#3#7???8000#3)##7???7000#100000001000+$28$25##18'+$28$25#1000#7?????????>8)$2-1000#1000+$28$25##18)$21##18+$28$25##18)##10000#6:6000+$28$25##18)$22##4+$28$25##18)$23##4+$28$25##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28$25!$2-58,8++$28$25#18!$2-50,8+$28@#18$2:!$2-48,8$21!$2-:8,8#;8980!$2-;0,8+$2-68,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 519100 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754692 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlH.

Module LibSegNa_azlI0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#18!$21#10,8+$24#18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#18!$2-58,8+$28#30!$2-50,8+$28#30!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#30+$28#30+$28#30&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#18!$21#10,8+$28#30!$2-58,8$24!$21#8,8+$28#30!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI0.

Module LibSegNa_azlI1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#30!$21#10,8+$24#30'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#30!$2-58,8+$28#48!$2-50,8+$28#60!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#60+$28#60+$28#48&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#30!$21#10,8+$28#60!$2-58,8$24!$21#8,8+$28#48!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI1.

End BndP_Na_043.
Module BndP_Na_044.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_044 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0e2eda2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI102BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI102BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI105XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI104planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlI103kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI92BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI92BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI95XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI94planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlI93kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlJ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044=LibSegNa_azlK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044>LibSegNa_azlS13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS102BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS102BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS105XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS104planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0169;BndP_Na_044?LibSegNa_azlS103kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_azlI10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#6000!$21#10,8+$24#6000'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#6000!$2-58,8+$28#6018!$2-50,8+$28#<000!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#<000+$28#<000+$28#6018&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#6000!$21#10,8+$28#<000!$2-58,8$24!$21#8,8+$28#6018!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI10.

Module LibSegNa_azlI2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#60!$21#10,8+$24#60'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#60!$2-58,8+$28#78!$2-50,8+$28#<0!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#<0+$28#<0+$28#78&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#60!$21#10,8+$28#<0!$2-58,8$24!$21#8,8+$28#78!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI2.

Module LibSegNa_azlI3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#<0!$21#10,8+$24#<0'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#<0!$2-58,8+$28#=8!$2-50,8+$28#180!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#180+$28#180+$28#=8&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#<0!$21#10,8+$28#180!$2-58,8$24!$21#8,8+$28#=8!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI3.

Module LibSegNa_azlI4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#180!$21#10,8+$24#180'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#180!$2-58,8+$28#198!$2-50,8+$28#300!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#300+$28#300+$28#198&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#180!$21#10,8+$28#300!$2-58,8$24!$21#8,8+$28#198!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI4.

Module LibSegNa_azlI5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#300!$21#10,8+$24#300'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#300!$2-58,8+$28#318!$2-50,8+$28#600!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#600+$28#600+$28#318&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#300!$21#10,8+$28#600!$2-58,8$24!$21#8,8+$28#318!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI5.

Module LibSegNa_azlI6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#600!$21#10,8+$24#600'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#600!$2-58,8+$28#618!$2-50,8+$28#<00!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#<00+$28#<00+$28#618&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#600!$21#10,8+$28#<00!$2-58,8$24!$21#8,8+$28#618!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI6.

Module LibSegNa_azlI7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#<00!$21#10,8+$24#<00'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#<00!$2-58,8+$28#<18!$2-50,8+$28#1800!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#1800+$28#1800+$28#<18&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#<00!$21#10,8+$28#1800!$2-58,8$24!$21#8,8+$28#<18!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI7.

Module LibSegNa_azlI8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#1800!$21#10,8+$24#1800'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#1800!$2-58,8+$28#1818!$2-50,8+$28#3000!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#3000+$28#3000+$28#1818&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#1800!$21#10,8+$28#3000!$2-58,8$24!$21#8,8+$28#1818!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI8.

Module LibSegNa_azlI9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [534948].
Definition STOPS1 : list Z := [534948] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7+$2-68$21$:$;$<$=$>$?$10$11$28#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$24!$21#8,8+$24#3000!$21#10,8+$24#3000'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-68,8$28!$2-60,8+$28#3000!$2-58,8+$28#3018!$2-50,8+$28#6000!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 756180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 33), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 33), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#829:4#829:4#5=#829:4,20##;8=6<+$2-80$3$4$5$6$7+$21#8$21$28+$28#6000+$28#6000+$28#3018&6+$21#10#3$?$10$11$23$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-80,8+$21#8!$2-78,8#;8744!$2-68,8$24!$2-50,8+$24#3000!$21#10,8+$28#6000!$2-58,8$24!$21#8,8+$28#3018!$2-60,8$24!$21#,8$28'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-88,8$21!$2-90,8$23!$2-98,8$22!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 534948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 756180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 756180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlI9.

Module LibSegNa_azlJ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#8$21$:$;$<$=$>$?$10$11$23$22$25+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$28!$21#8,8++$28$25#18!$21#10,8+$28@#18$2:'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10'$25#18#6000&$25#8'$2:#2#800!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-78,8#;8744!$2-80,8+$21#8!$2-68,8$24!$2-60,8$24!$2-58,8$24!$2-50,8+$24$25!$2-48,8$21"%pstring).
Definition ss0 : sym_state := SS 757100 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?1?<0#?1?<0#5=#?1?<0,20##;8758+$2-70$3$4$5$6$7+$21#8$21$24$25$24#7???8000$24+&6+$2-58#3#7???8000$10$11$23$22++$28$25#18+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-78,8#;8758'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#,8$28!$21#8,8++$28$25#18!$21#10,8+$28@#18$2:'$24#1000#7?????????>8&$24#10'$28#1000#7?????????=0&$28#10'$25#18#6000&$25#8'$2:#2#800!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-80,8+$21#8!$2-68,8$24!$2-60,8$24!$2-58,8$24!$2-50,8+$24$25!$2-48,8$21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 991168 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 757100 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 757100 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlJ.

Module LibSegNa_azlK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [755596].
Definition STOPS1 : list Z := [755596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7+$21#8$9$:$;$<$=$>$?$10$11$12$13$29+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$21#8,8$29!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32"%pstring).
Definition ss0 : sym_state := SS 755544 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;878<#;878<#5=#;878<,20#$2;$2$3$4$5$6$7$2<$2=+$29-18$;$<$=$>$?$10$11$2>$2?$30$31$32$17$18$19$1:$1;$1<$1=$1>$1?,,17!$21#8,8$29'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18($21##18!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 755596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 755544 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 755544 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlK.

Module LibSegNa_azlS0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#18!$21#10,8+$24#18'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#2$21#30#40#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#18+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#18!$21#10,8+$24#18'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS0.

Module LibSegNa_azlS1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#30!$21#10,8+$24#30'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#4$21#60#80#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#30+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#30!$21#10,8+$24#30'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS1.

Module LibSegNa_azlS10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0e2eda.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0e2eda.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#6000!$21#10,8+$24#6000'$24#1000#7?????????>8&$24#10"%pstring).
Definition ss0 : sym_state := SS 754920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##;8<;4+$2-80$3$4$5$6$7#800$21#<000#10000#555555555555555^#:#::::::::::::::;#::::::::::::::;$?$10$11$23$22#6000+&6+$21#8#3#7???8000#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-80,8+$21#8!$2-78,8#;8678!$2-48,8$21!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?802000#800000000000&$2#10($2-1000#1000#&6$2#3#7???7>00#200%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7?????????=?&$21#8)##7???7000#100000001000$21##18#&6$21#3#7???8000#3)$2-1000#1000$21##18)##10000#6:6000$21##18!$21#,8$24!$21#8,8+$24#6000!$21#10,8+$24#6000'$24#1000#7?????????>8&$24#10,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0e2eda.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 754920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0e2eda.IT BndT_Na_000.SegItab_Na_0e2eda.IT_sound BF NX0 BR XSTEP F0 PSS plan 754920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_azlS10.

End BndP_Na_044.
