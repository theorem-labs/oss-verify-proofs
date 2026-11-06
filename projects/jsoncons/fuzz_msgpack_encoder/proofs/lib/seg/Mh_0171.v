(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002 BndT_Na_000. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_072.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002 BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_072 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_bb7e442ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2a3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qkC2b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qkC33kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_1c89a22ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpA03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072=LibSegNa_qlpB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpBd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpC23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEA23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072?LibSegNa_qlpEO23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_072>LibSegNa_qlpH03kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qkC2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_bb7e44.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_bb7e44.IT.
Definition ENDS : list Z := [761780].
Definition STOPS1 : list Z := [761780] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7$8$9$2;$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487360 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 43) 1 1;
   KWord (SA (EVar 2) (-136)) 8 (EVar 47);
   KRange (EVar 47) 0 140737488355328].
Definition ss0 : sym_state := SS 761744 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9?;4#;9?;4#5=#;9?;4,20#$2?+$2-80$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?8010<0#800000000000&$2#20'$2;#1#1!$2-88,8$2?'$2?##800000000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761780 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_bb7e44.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 761744 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_bb7e44.IT BndT_Na_002.SegItab_Na_bb7e44.IT_sound BF NX0 BR XSTEP F0 PSS plan 761744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qkC2a.

Module LibSegNa_qkC2b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_bb7e44.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_bb7e44.IT.
Definition ENDS : list Z := [761856].
Definition STOPS1 : list Z := [761856; 761772] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7$8$9$2;$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#10'$2;###&6+$2-:0#3#7???8000#4)$2-<0#10&6+$2-:0#3#7???8000#4!$2-:0,8$28!$2-98,8$2<'$28##800000000000'$2<##800000000000'&4$28$2<##"%pstring).
Definition ss0 : sym_state := SS 761744 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-184), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-184), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;:000#;9?:<#;:000#5=#;:000,20##;9?:<+$2-;0$3$4$5$6$7$8$9#$2<+$2-98&6+$2-98#3$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$2-;8,8#;9?:<%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010<0#800000000000&$2#20($2-<0#10'$2;###&6+$2-:0#3#7???8000#4)$2-<0#10&6+$2-:0#3#7???8000#4!$2-:0,8$28!$2-98,8$2<'$28##800000000000'$2<##800000000000'&4$28$2<##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_bb7e44.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 761744 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_bb7e44.IT BndT_Na_002.SegItab_Na_bb7e44.IT_sound BF NX0 BR XSTEP F0 PSS plan 761744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qkC2b.

Module LibSegNa_qkC3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_bb7e44.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_bb7e44.IT.
Definition ENDS : list Z := [761780].
Definition STOPS1 : list Z := [761780] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-;0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487360 140737488355328;
   KAlign (EVar 2) 32;
   KWord (SA (EVar 2) (-136)) 8 (EVar 47);
   KRange (EVar 47) 0 140737488355328].
Definition ss0 : sym_state := SS 761772 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9?;4#;9?;4#5=#;9?;4,20#$2?+$2-80$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?8010<0#800000000000&$2#20!$2-88,8$2?'$2?##800000000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761780 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_bb7e44.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 761772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_bb7e44.IT BndT_Na_002.SegItab_Na_bb7e44.IT_sound BF NX0 BR XSTEP F0 PSS plan 761772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qkC3.

Module LibSegNa_qlpA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [412000].
Definition STOPS1 : list Z := [412000; 851500] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 36); (EVar 34); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487392 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-224)) (ELit 224)].
Definition ss0 : sym_state := SS 851380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64960#<?>2<#64960#5=#64960,20##<?>2<+$2->0$3$4$5$6$7$2+$2->0#60#15?:78#1$=$>$?$10$11$12$22$14$15#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-90,8$21!$2-88,8$24!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2->0,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010>0#800000000000&$2#20($2->0#>0,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851380 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpA0.

Module LibSegNa_qlpA16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [412000].
Definition STOPS1 : list Z := [412000; 851500] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2#10$3$4$5$6$7$8$9$21$24$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487392 140737488355312;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-224)) (ELit 240)].
Definition ss0 : sym_state := SS 851380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 240)].
Definition F0L : list SR.region := [((EVar 2), (-224), 240)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64960#<?>2<#64960#5=#64960,20##<?>2<+$2->0$3$4$5$6$7+$2#10+$2->0#60#15?:78#1$=$>$?$10$11$12$22$14$15#7???8000$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-90,8$21!$2-88,8$24!$2-58,8$1;!$2-50,8$1:!$2-48,8$19!$2-40,8$18!$2-38,8$17!$2-30,8$16!$2-28,8$15!$2-20,8$14!$2-18,8$13!$2-10,8$12!$2-8,8$9!$2#,8$8!$2#8,8$1!$2-=0,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010>0#7??????????0&$2#20($2->0#?0,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851380 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851380 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpA16.

Module LibSegNa_qlpB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [851920].
Definition STOPS1 : list Z := [851920] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$32$;$<$=$>$?$10$11$12$22$14$15#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?8010>0#800000000000&$2#20($2->0#50($2-70#8!$2-90,8$21!$2-88,8$24'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##18(&6$32#3#7???8000#<)+$2->0##>0$32##80'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#9#3#7???8000#1)$21##1?8$32##80)&6$32#3#7???8000#10&6+$21#9#3#7???8000#1!$21#9,1#"%pstring).
Definition ss0 : sym_state := SS 851500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 80); ((EVar 2), (-112), ELit 8); ((EVar 50), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-224), 80); ((EVar 2), (-112), 8); ((EVar 50), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<??=0#<??=0#5=#<??=0,20#$1+$2->0$3$4$5$6$7$8+$2->0+&6+$21#178#3#7???8000+&6$22#3#7???8000+&9$22#7#3+&6$24#3#7???8000+$21#178#$32$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000+$21#9+$21#8+$21#180+&6+$21#9#3#7???8000+&6$32#3#7???8000$1<$1=$1>$1?,,2>!$2-;8,8+&6+$21#178#3#7???8000!$2-<0,8+&6$24#3#7???8000!$2-:0,8+$21#178!$2-=8,8+&9$22#7#3!$2-98,8+&6$22#3#7???8000!$2-<8,8#!$2-=0,8#1!$2->0,8+$32#20!$2-70,8$32!$2-:8,8$32!&6$32#3#7???800;,1^#?#??????????????3!&6$32#3#7???800:,1^#?#??????????????3!&6$32#3#7???8009,1^#?#??????????????3!&6$32#3#7???8008,1^#?#??????????????3!&6$32#3#7???8007,1^#?#??????????????3!&6$32#3#7???8006,1^#?#??????????????8!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8!&6$32#3#7???8003,1^#?#??????????????1!&6$32#3#7???8002,1^#?#??????????????1!&6$32#3#7???8001,1^#?#??????????????1!&6$32#3#7???8000,1^#?#??????????????1!$32#10,8#<?=;4!$32#8,8#15:7=!$32#,8#41;58:;3!$2-;0,8$32'$2#7???7?8010>0#800000000000&$2#20($2->0#50($2-70#8!$2-90,8$21!$2-88,8$24'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##18(&6$32#3#7???8000#<)+$2->0##>0$32##80'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#9#3#7???8000#1)$21##1?8$32##80)&6$32#3#7???8000#10&6+$21#9#3#7???8000#1!$21#9,1#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 851920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpB.

Module LibSegNa_qlpBd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [851692].
Definition STOPS1 : list Z := [851692] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$32$;$<$=$>$?$10$11$12$22$14$15#7???8000$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?8010>0#800000000000&$2#20($2->0#50($2-70#8!$2-90,8$21!$2-88,8$24'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##18(&6$32#3#7???8000#<)+$2->0##>0$32##80'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#9#3#7???8000#1)$21##1?8$32##80)&6$32#3#7???8000#10&6+$21#9#3#7???8000#1!$21#9,1#1"%pstring).
Definition ss0 : sym_state := SS 851500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 80); ((EVar 2), (-112), ELit 8); ((EVar 50), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-224), 80); ((EVar 2), (-112), 8); ((EVar 50), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?>><#<?>><#5=#<?>><,20#$1+$2->0$3$4$5$6$7$8+$2->0#1#15:7=#<?=;4^#?#??????????????3^#?#??????????????8^#?#??????????????1$32$11$12$22$14$15#7???8000+$21#9$18$19+&6+$21#9#3#7???8000+&6$32#3#7???8000$1<$1=$1>$1?,,26!$2-70,8$32!$2-:8,8$32!&6$32#3#7???800;,1^#?#??????????????3!&6$32#3#7???800:,1^#?#??????????????3!&6$32#3#7???8009,1^#?#??????????????3!&6$32#3#7???8008,1^#?#??????????????3!&6$32#3#7???8007,1^#?#??????????????3!&6$32#3#7???8006,1^#?#??????????????8!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8!&6$32#3#7???8003,1^#?#??????????????1!&6$32#3#7???8002,1^#?#??????????????1!&6$32#3#7???8001,1^#?#??????????????1!&6$32#3#7???8000,1^#?#??????????????1!$32#10,8#<?=;4!$32#8,8#15:7=!$32#,8#41;58:;3!$2-;0,8$32'$2#7???7?8010>0#800000000000&$2#20($2->0#50($2-70#8!$2-90,8$21!$2-88,8$24'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##18(&6$32#3#7???8000#<)+$2->0##>0$32##80'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#9#3#7???8000#1)$21##1?8$32##80)&6$32#3#7???8000#10&6+$21#9#3#7???8000#1!$21#9,1#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 851692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpBd.

Module LibSegNa_qlpC1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [732160].
Definition STOPS1 : list Z := [732160; 852480] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14+&6+$21#8#3#7???8000#7???8000+$21#9+$21#8$19+&6+$21#9#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#9#3#7???8000#1($21#8#2'$2#7???7?8010>0#800000000000&$2#20!$2-<0,8+&6$24#3#7???8000!$2-88,8$24'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;8#1)$2->0#>0$24##8)$21#8#2$24##8"%pstring).
Definition ss0 : sym_state := SS 852400 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 2)].
Definition F0L : list SR.region := [((EVar 33), (8), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;2<00#=0200#;2<00#5=#;2<00,20##=0200+$2->0$3$4$5$6$7$8+$2->0$24#;2<00$24$=$>$?$10$11$12$13$14+&6+$21#8#3#7???8000#7???8000+$21#9+$21#8$19+&6+$21#9#3#7???8000$1;$1<$1=$1>$1?,,16!$21#9,1#1!$21#8,1#%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#9#3#7???8000#1($21#8#2'$2#7???7?8010>0#800000000000&$2#20!$2-<0,8+&6$24#3#7???8000!$2-88,8$24'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;8#1)$2->0#>0$24##8)$21#8#2$24##8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 732160 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpC1.

Module LibSegNa_qlpC2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [851692].
Definition STOPS1 : list Z := [851692] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16+$21#9$18$19+&6+$21#9#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488354824;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 504);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (9))) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 33) 9) 1 (ELit 1)].
Definition ss0 : sym_state := SS 852480 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?>><#<?>><#5=#<?>><,20#$1+$2->0$3$4$5$6$7$8$9#1$;$<$=$>$?$10$11$12$13$14$15$16+$21#9$18$19+&6+$21#9#3#7???8000$1;$1<$1=$1>$1?,,5'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#9#3#7???8000#1!$21#9,1#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 851692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852480 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpC2.

Module LibSegNa_qlpEA1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [723212].
Definition STOPS1 : list Z := [723212; 862328] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$21$24$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15%#10000#158000!##15?:78,8#7???8000'$2#7???7?801100#800000000000&$2#20($2-?8#18'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#<#3#7???8000#1!$21#<,4$2='$2=#1#401($21#<#4'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;4#1)$2-100#20$24##8)$21#<#4$24##8"%pstring).
Definition ss0 : sym_state := SS 862208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-248), ELit 24); ((EVar 33), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-248), 24); ((EVar 33), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;090<#=2878#;090<#5=#;090<,20##=2878+$2-100$3$4$5$6$7$21#7???8000$24$21$22#;090<#$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$21#<,4+$2=-1!$2-?8,8$9!$2-?0,8$8!$2->8,8$1%#10000#158000!##15?:78,8#7???8000'$2#7???7?801100#800000000000&$2#20($2-?8#18'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#<#3#7???8000#1'$2=#1#401($21#<#4'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;4#1)$2-100#20$24##8)$21#<#4$24##8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 723212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 862208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 862208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpEA1.

Module LibSegNa_qlpEA2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [790344].
Definition STOPS1 : list Z := [790344; 852500] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15%#10000#158000'$2#7???7?801100#800000000000&$2#20!$2->8,8#=0214!$2-?0,8$2>!$2-?8,8$2?'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#10#3#7???8000#1#&6+$21#178#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#10,1#($21#8#1!$21#178,8$2;!$21#180,8$28($21#180#8'$28#1018#800000000000'$2;#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 862328 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EVar 33), (384), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EVar 33), (384), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<0?48#=0214#<0?48#5=#<0?48,20##=0214+$2->0$3$4$5$6$7$2>$2?+$21#178@^-5-555555555555555&7+$28@-1$2;#3+$21#178+$28-18^#:#::::::::::::::;$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$21#180,8+$28-18!$21#8,1#1%#10000#158000'$2#7???7?801100#800000000000&$2#20!$2->8,8#=0214!$2-?0,8$2>!$2-?8,8$2?'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#10#3#7???8000#1#&6+$21#178#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#10,1#($21#8#1!$21#178,8$2;($21#180#8'$28#1018#800000000000'$2;#1000#800000000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 790344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 862328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 862328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpEA2.

Module LibSegNa_qlpEO1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [733340].
Definition STOPS1 : list Z := [733340; 862672] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$21$24$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15%#10000#158000!##15?:78,8#7???8000'$2#7???7?801100#800000000000&$2#20($2-?8#18'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#<#3#7???8000#1!$21#<,4$2='$2=#1#401($21#<#4'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;;#1)$2-100#20$24##8)$21#<#4$24##8"%pstring).
Definition ss0 : sym_state := SS 862552 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-248), ELit 24); ((EVar 33), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-248), 24); ((EVar 33), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;309<#=29=0#;309<#5=#;309<,20##=29=0+$2-100$3$4$5$6$7$21#7???8000$24$21$22#;309<#$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$21#<,4+$2=-1!$2-?8,8$9!$2-?0,8$8!$2->8,8$1%#10000#158000!##15?:78,8#7???8000'$2#7???7?801100#800000000000&$2#20($2-?8#18'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#<#3#7???8000#1'$2=#1#401($21#<#4'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60#&6$24#3#7???8000#1!$24#,8#150=88###800221;;#1)$2-100#20$24##8)$21#<#4$24##8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 733340 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 862552 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 862552 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpEO1.

Module LibSegNa_qlpEO2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [790344].
Definition STOPS1 : list Z := [790344; 852520] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-100$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15%#10000#158000'$2#7???7?801100#800000000000&$2#20!$2->8,8#=0228!$2-?0,8$2>!$2-?8,8$2?'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#10#3#7???8000#1#&6+$21#178#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#10,1#($21#8#1!$21#178,8$2;!$21#180,8$28($21#180#8'$28#1018#800000000000'$2;#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 862672 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EVar 33), (384), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EVar 33), (384), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<0?48#=0228#<0?48#5=#<0?48,20##=0228+$2->0$3$4$5$6$7$2>$2?+$21#178@^-5-555555555555555&7+$28@-1$2;#3+$21#178+$28-18^#:#::::::::::::::;$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$21#180,8+$28-18!$21#8,1#1%#10000#158000'$2#7???7?801100#800000000000&$2#20!$2->8,8#=0228!$2-?0,8$2>!$2-?8,8$2?'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-100#20$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#10#3#7???8000#1#&6+$21#178#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#10,1#($21#8#1!$21#178,8$2;($21#180#8'$28#1018#800000000000'$2;#1000#800000000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 790344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 862672 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 862672 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpEO2.

Module LibSegNa_qlpH0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [853276].
Definition STOPS1 : list Z := [853276; 852032] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#($28-18#4'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (-24), ELit 4)].
Definition F0L : list SR.region := [((EVar 40), (-24), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=051<#=0040#=051<#5=#=051<,20##=0040+$2->0$3$4$5$6$7$8+$2->0$21$24$22$28+&6+$28-18#3#7???8000$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,15!$28-18,4#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8($28-18#4'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 853276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH0.

End BndP_Na_072.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002 BndT_Na_003.
Module BndP_Na_097.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002 BndT_Na_003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_097 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_89918d2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC212BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC213NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC212BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC215XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC212F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC213PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC214planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC215regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC213kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC222BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC223NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC222BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC225XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC222F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC223PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC224planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC225regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzC223kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD002BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD003NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD002BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD005XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD002F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD003PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD004planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD005regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD003kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD102BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD102BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD105XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD104planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD103kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD112BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD113NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD112BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD115XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD112F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD113PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD114planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD115regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD113kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD202BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD203NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD202BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD205XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD202F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD203PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD204planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD205regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD203kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD212BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD213NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD212BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD215XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD212F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD213PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD214planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD215regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD213kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD222BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD223NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD222BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD225XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD222F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD223PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD224planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD225regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD223kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD232BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD233NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD232BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD235XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD232F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD233PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD234planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD235regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097?LibSegNa_qrzD233kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_f955732ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspGS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097>LibSegNa_qspLI3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_097=LibSegNa_qspN3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qrzC21.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#1$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##!$21#8,8#2"%pstring).
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#1$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,9!$21#8,8#1'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzC21.

Module LibSegNa_qrzC22.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#2$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##!$21#8,8#2"%pstring).
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#2$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,9!$21#8,8#2'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzC22.

Module LibSegNa_qrzD00.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 4);
   KWr (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 8) 8 (ELit 0)].
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,6!$21#8,8#'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD00.

Module LibSegNa_qrzD10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#1+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 4);
   KWr (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 8) 8 (ELit 1)].
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#1+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,6!$21#8,8#'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD10.

Module LibSegNa_qrzD11.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#1$21+$21#8$16$17#7???8000#1+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 4);
   KWr (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 8) 8 (ELit 1)].
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#1$21+$21#8$16$17#7???8000#1+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,6!$21#8,8#1'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD11.

Module LibSegNa_qrzD20.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 4);
   KWr (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 8) 8 (ELit 2)].
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,6!$21#8,8#'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD20.

Module LibSegNa_qrzD21.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#1$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 4);
   KWr (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 8) 8 (ELit 2)].
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#1$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,6!$21#8,8#1'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD21.

Module LibSegNa_qrzD22.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [827888].
Definition STOPS1 : list Z := [827888; 828108; 827840; 828204; 827748] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#2$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488355296;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 32);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 4);
   KWr (SA (EVar 33) 0) (ELit 32);
   KWord (SA (EVar 33) 8) 8 (ELit 2)].
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#2$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,6!$21#8,8#2'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD22.

Module LibSegNa_qrzD23.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_89918d.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_89918d.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280; 828108; 828204; 828212; 828092; 827888] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#3$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1#1#1!$21#8,8#2!$21#18,8$25'$25#1000#7?????????<0"%pstring).
Definition ss0 : sym_state := SS 827732 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#7?058#<:2<<#<:32<#<:334#<:2;<#<:1?0#7?058#5=#7?058,20##<:1?0$2$3$4$5$6$7$8$9+$25#10##8$=$>$?$10$11$12#3$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,;!$21#8,8#3'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1#1#1!$21#18,8$25'$25#1000#7?????????<0,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_89918d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 827732 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_89918d.IT BndT_Na_002.SegItab_Na_89918d.IT_sound BF NX0 BR XSTEP F0 PSS plan 827732 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrzD23.

Module LibSegNa_qspD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_f95573.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_f95573.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$38$:$36$;$<$=$>$?$10$11$29$26$27$28$25$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$28#1:#80000001"%pstring).
Definition ss0 : sym_state := SS 1001236 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?1?<0#?1?<0#5=#?1?<0,20##?4728+$2-40$3$4$5$6$7$38$:$29$28$<$=$>$?$10$11$29$26$27$28$25$17$18$19$1:$1;$1<$1=$1>$1?,,10'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$28#1:#80000001,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_f95573.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1001236 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_f95573.IT BndT_Na_003.SegItab_Na_f95573.IT_sound BF NX0 BR XSTEP F0 PSS plan 1001236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qspD.

Module LibSegNa_qspGS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_f95573.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_f95573.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$:#,1#2<'$;##??"%pstring).
Definition ss0 : sym_state := SS 1001024 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##?4704+$2-40$3$4$5$6$7$;$:#30$;#2<$=$>$?$10$11+$:#1#30#16#17$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$:#,1#2<'$;##??,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_f95573.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1001024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_f95573.IT BndT_Na_003.SegItab_Na_f95573.IT_sound BF NX0 BR XSTEP F0 PSS plan 1001024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qspGS.

Module LibSegNa_qspLG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_f95573.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_f95573.IT.
Definition ENDS : list Z := [1001328; 1374112].
Definition STOPS1 : list Z := [1001328; 1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#80000001!$:#8,8$22'$22##80000000!$:#10,8$23'$23#1000#800000000000'$;##??'&4&1$22+@#2&6$24#1-1#1#1#1"%pstring).
Definition ss0 : sym_state := SS 1001024 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#?4770#14?7:0#?4770#14?7:0#5=#14?7:0,20##?4704+$2-40$3$4$5$6$7$;$:+@#8&6+@#4&6$24#1-2#3#8#<$21$=$>$?$10$11$23+@#8&6+@#4&6$24#1-2#3#8+@#2&6$24#1-1@#2&6$24#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#80000001!$:#8,8$22'$22##80000000!$:#10,8$23'$23#1000#800000000000'$;##??'&4&1$22+@#2&6$24#1-1#1#1#1,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_f95573.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1001024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_f95573.IT BndT_Na_003.SegItab_Na_f95573.IT_sound BF NX0 BR XSTEP F0 PSS plan 1001024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qspLG.

Module LibSegNa_qspLI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_f95573.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_f95573.IT.
Definition ENDS : list Z := [1001328; 1374112].
Definition STOPS1 : list Z := [1001328; 1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#80000001!$:#8,8$22'$22##80000000!$:#10,8$23'$23#1000#800000000000'$;##??'&4&1$22+@#2&6$24#1-1#1##(+$23$22##2)+$23$22##2$:##18)+$23$22##2$2-40#40"%pstring).
Definition ss0 : sym_state := SS 1001024 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 10), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 35) (EVar 34)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 10), (0), 24); ((EAlu Instr.ALU_ADD (EVar 35) (EVar 34)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#?4770#14?7:0#?4770#14?7:0#5=#?4770,20#$1$2$3$4$5$6$7$8$9+$22$23+$22#1$21$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!+$22$23#1,1#!+$22$23#,1$;!$:#8,8+$22#1!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8$24'&9$24#1#1#1'$24#1;#80000001'$22##80000000!$:#10,8$23'$23#1000#800000000000'$;##??'&4&1$22+@#2&6$24#1-1#1##(+$23$22##2)+$23$22##2$:##18)+$23$22##2$2-40#40,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1001328 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_f95573.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1001024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_f95573.IT BndT_Na_003.SegItab_Na_f95573.IT_sound BF NX0 BR XSTEP F0 PSS plan 1001024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qspLI.

Module LibSegNa_qspN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_f95573.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_f95573.IT.
Definition ENDS : list Z := [519092].
Definition STOPS1 : list Z := [519092] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$38$:$25$;$<$=$>$?$10$11$29$26$27$28$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33"%pstring).
Definition ss0 : sym_state := SS 1001220 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;4#7>;;4#5=#7>;;4,20##?4714+$2-40$3$4$5$6$7$38$:$25$29$27$=$>$?$10$11$29$26$27$28$25$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#6;6000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_f95573.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1001220 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_f95573.IT BndT_Na_003.SegItab_Na_f95573.IT_sound BF NX0 BR XSTEP F0 PSS plan 1001220 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qspN.

End BndP_Na_097.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000.
Module BndP_Na_073.
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
Ltac2 kr_t_BndP_Na_073 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_1c89a22ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH2e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073?LibSegNa_qlpH3e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpH43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpHX3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073=LibSegNa_qlpJ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQb3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQc3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQe3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_073>LibSegNa_qlpQz3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qlpH1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [790344].
Definition STOPS1 : list Z := [790344; 852400] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$13+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1#&6+$21#178#3#7???8000#1!$21#178,8$2;!$21#180,8+$2;#18'$2;#1000#7?????????>8)##10000#140000$2;##18&$2;#8)##7???7000#100000001000$2;##18#&6$2;#3#7???8000#3!$2;#,4#1($21#180#8)$2;##18$21##1?8'$2#7???7?8010>0#800000000000&$2#20!$2-;8,8+&6+$21#178#3#7???8000!$2-:0,8+$21#178"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (384), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (384), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<0?48#=01;0#<0?48#5=#<0?48,20##=01;0+$2->0$3$4$5$6$7$8+$2->0+$21#178#1#4#18+&6$2;#3#7???8000$?$10$11#2384<$13+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,17!$21#180,8$2;%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1#&6+$21#178#3#7???8000#1!$21#178,8$2;'$2;#1000#7?????????>8)##10000#140000$2;##18&$2;#8)##7???7000#100000001000$2;##18#&6$2;#3#7???8000#3!$2;#,4#1($21#180#8)$2;##18$21##1?8'$2#7???7?8010>0#800000000000&$2#20!$2-;8,8+&6+$21#178#3#7???8000!$2-:0,8+$21#178,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 790344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH1.

Module LibSegNa_qlpH2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [853276; 862208].
Definition STOPS1 : list Z := [853276; 862208; 852196; 852500] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#2!$28-8,8$29!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-8#8'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 40), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=051<#=2800#=00>4#=0214#=051<#=2800#5;#=00<0,20#$1+$2->0$3$4$5$6$7$8+$2->0+$28-8$2:+&6+$28-8#3#7???8000$29#$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,1:%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#2!$28-8,8$29!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-8#8'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=051<#=2800#=00>4#=0214#=051<#=2800#5=#=051<,20##=00>4+$2->0$3$4$5$6$7$8+$2->0$21$24$22+$29#1#$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,1:!$28-8,8+$29#1'&4$29$2:#1#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#2!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-8#8'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=051<#=2800#=00>4#=0214#=051<#=2800#5=#=2800,20##=0214+$2->0$3$4$5$6$7$8+$2->0$21$24$22$29#$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,1;'&4$29$2:##%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#2!$28-8,8$29!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-8#8'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 853276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 862208 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH2.

Module LibSegNa_qlpH2e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [862208].
Definition STOPS1 : list Z := [862208; 852500] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#2!$28-8,8$29!$28-10,8$29'$29#^#?#???????????????'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2800#=0214#=2800#5=#=2800,20##=0214+$2->0$3$4$5$6$7$8+$2->0$21$24$22$29#$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,18%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#2!$28-8,8$29!$28-10,8$29'$29#^#?#???????????????'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 862208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH2e.

Module LibSegNa_qlpH3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [853276; 862552].
Definition STOPS1 : list Z := [853276; 862552; 852320; 852520] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#3!$28-8,8$29!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-18#18'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (-24), ELit 4); ((EVar 40), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 40), (-24), 4); ((EVar 40), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=051<#=2958#=0160#=0228#=051<#=2958#5;#=012<,20#$1+$2->0$3$4$5$6$7$8+$2->0+$28-18+$28-8$2:$29+&6+$28-18#3#7???8000+&6+$28-8#3#7???8000#$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,1:%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#3!$28-8,8$29!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-18#18'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=051<#=2958#=0160#=0228#=051<#=2958#5=#=051<,20##=0160+$2->0$3$4$5$6$7$8+$2->0$21$24$22+$29#1+&6+$28-18#3#7???8000+&6+$28-8#3#7???8000#$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,1:!$28-18,4#4!$28-8,8+$29#1'&4$29$2:#1#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-18#18'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=051<#=2958#=0160#=0228#=051<#=2958#5=#=2958,20##=0228+$2->0$3$4$5$6$7$8+$2->0$21$24$22$29+&6+$28-18#3#7???8000+&6+$28-8#3#7???8000#$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,1;'&4$29$2:##%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#3!$28-8,8$29!$28-10,8$2:'$29#^#?#??????????????>'$2:#^#?#???????????????($28-18#18'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 853276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 862552 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH3.

Module LibSegNa_qlpH3e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [862552].
Definition STOPS1 : list Z := [862552; 852520] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#3!$28-8,8$29!$28-10,8$29'$29#^#?#???????????????'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=2958#=0228#=2958#5=#=2958,20##=0228+$2->0$3$4$5$6$7$8+$2->0$21$24$22$29+&6+$28-18#3#7???8000+&6+$28-8#3#7???8000#$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,18%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#3!$28-8,8$29!$28-10,8$29'$29#^#?#???????????????'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 862552 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH3e.

Module LibSegNa_qlpH4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [853276].
Definition STOPS1 : list Z := [853276; 852088] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16%#10000#158000'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8!$28-18,4#4($28-18#4'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24"%pstring).
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 40), (-24), ELit 4)].
Definition F0L : list SR.region := [((EVar 40), (-24), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#=051<#=0078#=051<#5=#=051<,20##=0078+$2->0$3$4$5$6$7$8+$2->0$21$24$22$28+&6+$28-18#3#7???8000$?$10$11#2384<$22+&6+$21#180#3#7???8000+&6+$21#8#3#7???8000#7???8000$17+$21#8+$21#180$1:$1;$1<$1=$1>$1?,,15!$28-18,4#3'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2->0#>0$21##1?8#&6+$21#8#3#7???8000#1#&6+$21#180#3#7???8000#1!$21#8,1#1!$21#180,8$28'$28#1018#800000000000)##10000#140000$28-18#18&$28#8)##7???7000#100000001000+$28-18##18#&6+$28-18#3#7???8000#3)$28-18#18$2->0#>0)$28-18#18$21##1?8($28-18#4'$2#7???7?8010>0#800000000000&$2#20!$2-90,8$21!$2-88,8$24,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 853276 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpH4.

Module LibSegNa_qlpHX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [851692].
Definition STOPS1 : list Z := [851692] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14+&6+$21#8#3#7???8000$16$17+$21#8$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488354824;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 504);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (8))) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 33) 8) 1 (ELit 0)].
Definition ss0 : sym_state := SS 851920 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?>><#<?>><#5=#<?>><,20#$1+$2->0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14+&6+$21#8#3#7???8000$16$17+$21#8$19$1:$1;$1<$1=$1>$1?,,5'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1!$21#8,1#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 851692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpHX.

Module LibSegNa_qlpJ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [851920].
Definition STOPS1 : list Z := [851920] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16+$21#9$18$19+&6+$21#9#3#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 7036928 140737488354824;
   KAlign (EVar 33) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 33) 0) (ELit 504);
   KZero (SA (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (9))) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 33) 9) 1 (ELit 0)].
Definition ss0 : sym_state := SS 852500 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<??=0#<??=0#5=#<??=0,20#$1+$2->0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16+$21#9$18$19+&6+$21#9#3#7???8000$1;$1<$1=$1>$1?,,5'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#9#3#7???8000#1!$21#9,1#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 851920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpJ.

Module LibSegNa_qlpQa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [852332].
Definition STOPS1 : list Z := [852332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 852032 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=016<#=016<#5=#=016<,20#$1+$2->0$3$4$5$6$7$8+$2->0#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 852332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpQa.

Module LibSegNa_qlpQb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [852332].
Definition STOPS1 : list Z := [852332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 852088 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=016<#=016<#5=#=016<,20#$1+$2->0$3$4$5$6$7$8+$2->0#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 852332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852088 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852088 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpQb.

Module LibSegNa_qlpQc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [852332].
Definition STOPS1 : list Z := [852332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 852196 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=016<#=016<#5=#=016<,20#$1+$2->0$3$4$5$6$7$8+$2->0#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 852332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852196 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852196 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpQc.

Module LibSegNa_qlpQd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [852332].
Definition STOPS1 : list Z := [852332] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 852320 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=016<#=016<#5=#=016<,20#$1+$2->0$3$4$5$6$7$8+$2->0#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'$2#7???7?8010>0#800000000000&$2#20!$2-98,8+&6$22#3#7???8000'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 852332 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpQd.

Module LibSegNa_qlpQe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [851692].
Definition STOPS1 : list Z := [851692] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 34) 7036928 140737488355312;
   KAlign (EVar 34) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) 0) (ELit 16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 34) 0) 4 (EVar 44);
   KRange (EVar 44) 1 64].
Definition ss0 : sym_state := SS 852332 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?>><#<?>><#5=#<?>><,20#$1+$2->0$3$4$5$6$7$8$9$2<$;$<$=$>$?$10$11$12$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1!$22#,4$2<'$2<#1#40,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 851692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852332 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852332 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpQe.

Module LibSegNa_qlpQz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [852520].
Definition STOPS1 : list Z := [852520] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 34) 7036928 140737488355312;
   KAlign (EVar 34) 8;
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) 0) (ELit 16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 34) 0) 4 (ELit 0)].
Definition ss0 : sym_state := SS 852332 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=0228#=0228#5=#=0228,20#$1+$2->0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$22$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$22#6;6000#7??????????0&$22#8)##7???7000#100000001000$22##10#&6$22#3#7???8000#1!$22#,4#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 852520 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852332 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852332 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpQz.

End BndP_Na_073.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002.
Module BndP_Na_102.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_102 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_b3c5092ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwC23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwD23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102>LibSegNa_qtwF13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102=LibSegNa_qtwG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102@LibSegNa_qtwH1c13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0m3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1e0p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102ALibSegNa_qtwH1f1d3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0171;BndP_Na_102?LibSegNa_qtwR0a3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qtwC1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [999896].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1!$32#28,8#1"%pstring).
Definition ss0 : sym_state := SS 867924 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#?41=8#5=#?41=8,20##=3>78+$2->0$3$4$5$6$7$8+$2->0$2=#17$<$=$>$?$10$11#1+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?,,='$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1!$32#28,8#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 999896 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867924 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwC1.

Module LibSegNa_qtwC2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [999896].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1!$32#28,8#2"%pstring).
Definition ss0 : sym_state := SS 867924 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#?41=8#5=#?41=8,20##=3>78+$2->0$3$4$5$6$7$8+$2->0$2=#2<$<$=$>$?$10$11#2+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?,,='$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1!$32#28,8#2,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 999896 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867924 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwC2.

Module LibSegNa_qtwD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#1+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100"%pstring).
Definition ss0 : sym_state := SS 867960 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-216), ELit 40); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 4); ((EVar 50), (96), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-216), 40); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 4); ((EVar 50), (96), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#7?058#5=#7?058,20##=3>;<+$2->0$3$4$5$6$7$8+$2->0+$32#68##18$=$>$?$10$11#1+&6$32#3#7???8000$2=+$32#60$32+$32#68+$32#20$21$1:$1;$1<$1=$1>$1?,,13!$32#60,1#!&6$32#3#7???800?,1#!$2-<0,8+&6$32#3#7???8000!&6$32#3#7???800>,1#!&6$32#3#7???800=,1#!&6$32#3#7???800<,1#!$2-=0,8$32!$2-<8,8$32!$2-;8,8#7???8000!$2-=8,8$21'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867960 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867960 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwD.

Module LibSegNa_qtwD2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#2+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100"%pstring).
Definition ss0 : sym_state := SS 867960 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-216), ELit 40); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 4); ((EVar 50), (96), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-216), 40); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 4); ((EVar 50), (96), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#7?058#5=#7?058,20##=3>;<+$2->0$3$4$5$6$7$8+$2->0+$32#68##18$=$>$?$10$11#2+&6$32#3#7???8000$2=+$32#60$32+$32#68+$32#20$21$1:$1;$1<$1=$1>$1?,,13!$32#60,1#!&6$32#3#7???800?,1#!$2-<0,8+&6$32#3#7???8000!&6$32#3#7???800>,1#!&6$32#3#7???800=,1#!&6$32#3#7???800<,1#!$2-=0,8$32!$2-<8,8$32!$2-;8,8#7???8000!$2-=8,8$21'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867960 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867960 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwD2.

Module LibSegNa_qtwE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [817564].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14+$32#60$16$17+$32#20$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KRange (EVar 2) 140735332487392 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-224)) (ELit 224);
   KRange (EVar 50) 7036928 140737488355072].
Definition ss0 : sym_state := SS 868028 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 16); ((EVar 2), (-136), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-176), 16); ((EVar 2), (-136), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#<799<#5=#<799<,20##=3?0<+$2->0$3$4$5$6$7$8+$2->0+$32#20+$2-88+$32#20+$32#60#1$?$10$11#:$13$14+$32#60^#<#<<<<<<<<<<<<<<=$17+$32#20#12$1:$1;$1<$1=$1>$1?,,;!$2-;0,8+$32#20!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-88,1#!$2-:8,8+$32#70%#10000#158000'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 817564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868028 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwE.

Module LibSegNa_qtwF0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [868180].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14+$32#60$16+$32#68+$32#20$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$32#60,1$27'$27##??'&9$27#1##!$2-:8,8+$32#70!$32#68,8#!$32#28,8$25'$25##1"%pstring).
Definition ss0 : sym_state := SS 868108 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,10#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3?54#5=#=3?54,20#$1+$2->0$3$4$5$6$7$8+$2->0##$<$=$>$?$10$11$12$13$14+$32#60$16+$32#68#$19@-1$25$25$1<$1=$1>$1?,,:'$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$32#60,1$27'$27##??'&9$27#1##!$2-:8,8+$32#70!$32#68,8#!$32#28,8$25'$25##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 868180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868108 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868108 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwF0.

Module LibSegNa_qtwF1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [868180].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$14+$32#60$16+$32#68+$32#20$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$32#60,1$27'$27##??'&9$27#1##!$2-:8,8+$32#70!$32#68,8#1!$32#28,8$25'$25##1!$2-;8,8#7???8000&$32#20)##7???7000#100000001000$32##100#&6+$32#70#3#7???8000#1!$32#70,8$22"%pstring).
Definition ss0 : sym_state := SS 868108 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,10#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3?54#5=#=3?54,20#$1+$2->0$3$4$5$6$7$8+$2->0###7???8000$=$>$?$10$11$12$13$14+$32#60$16+$32#68$22$19@-1$25$25$1<$1=$1>$1?,,?'$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$32#60,1$27'$27##??'&9$27#1##!$2-:8,8+$32#70!$32#68,8#1!$32#28,8$25'$25##1!$2-;8,8#7???8000&$32#20)##7???7000#100000001000$32##100#&6+$32#70#3#7???8000#1!$32#70,8$22,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 868180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868108 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868108 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwF1.

Module LibSegNa_qtwG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$23$;$<$=$>$?$10$11#:$13$2=$15^#<#<<<<<<<<<<<<<<=$17$22$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 34) 0 18446744073709551615;
   KRange (EVar 35) 0 18].
Definition ss0 : sym_state := SS 868180 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#?4640#5=#?4640,20##=3?7<$2$3$4$5$6$7$8$9$2=&9+&9%1$22@#:&6/3$22^#<#<<<<<<<<<<<<<<=#3-31#30#??$<$=$>$?$10$11#:$23$2=$15^#<#<<<<<<<<<<<<<<=$17&6/3$22^#<#<<<<<<<<<<<<<<=#3$19$1:$1;$1<$1=$1>$1?,,2'$22#^#?#???????????????'$23##12,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwG.

Module LibSegNa_qtwH1c0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [868180].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180; 868232] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; (EVar 35); EVar 20; EVar 21; EVar 22; EVar 23; (EVar 34); (ELit 18); (ELit 0); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 34) 1 18446744073709551615;
   KRange (EVar 35) 0 17].
Definition ss0 : sym_state := SS 868220 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3?88#=3?54#5=#=3?54,20#$1$2$3$4$5$6$7$8$9+$23#1$;$<$=$>$?$10$11$12$23$14$15$16$17$22#12#$1;$1<$1=$1>$1?,,2'$22#1^#?#???????????????'$23##11,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 868180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868220 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868220 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwH1c0.

Module LibSegNa_qtwH1c1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [868180].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180; 868232] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$23$14$15$16$17$22#12^#?#???????????????$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 34) 0 18446744073709551614;
   KRange (EVar 35) 0 17].
Definition ss0 : sym_state := SS 868220 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3?88#=3?54#5=#=3?54,20#$1$2$3$4$5$6$7$8$9+$23#1$;$<$=$>$?$10$11$12$23$14$15$16$17$22#12^#?#???????????????$1;$1<$1=$1>$1?,,2'$22#^#?#??????????????>'$23##11,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 868180 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868220 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868220 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwH1c1.

Module LibSegNa_qtwH1e0m.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [1001024].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180; 868084; 868288] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$2=$15$16$17#$19##$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$2-;0,8+$32#20!$2-=8,8$21!$2-;8,8#7???8000'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#1!$21#,1$26'$26##??'&9$26#2#2#2"%pstring).
Definition ss0 : sym_state := SS 868220 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,12#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3>?4#=3?<0#?4640#5=#?4640,20##=3?<0+$2->0$3$4$5$6$7$8+$2->0$2=#2=#$=$>$?$10$11#7???8000$13$2=$15$16$17+$32#20$19##$1<$1=$1>$1?,,='$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$2-;0,8+$32#20!$2-=8,8$21!$2-;8,8#7???8000'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#1!$21#,1$26'$26##??'&9$26#2#2#2,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868220 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868220 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwH1e0m.

Module LibSegNa_qtwH1e0p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [868288].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180; 868084; 868288] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12$13$2=$15$16$17#$19##$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$2-;0,8+$32#20!$2-=8,8$21!$2-;8,8#7???8000'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#1!$21#,1$26'$26##??'&9$26#2##"%pstring).
Definition ss0 : sym_state := SS 868220 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,12#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3>?4#=3?<0#=3?<0#5=#=3?<0,20#$1+$2->0$3$4$5$6$7$8+$2->0#+&6$21#3#7???8000#$=$>$?$10$11#7???8000$13$2=$15$16$17+$32#20$19##$1<$1=$1>$1?,,='$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$2-;0,8+$32#20!$2-=8,8$21!$2-;8,8#7???8000'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#1!$21#,1$26'$26##??'&9$26#2##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 868288 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868220 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868220 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwH1e0p.

Module LibSegNa_qtwH1f1d.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [817564].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868180; 868240] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12#12$14+$32#60$16$17$22#12^#?#???????????????#1$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487392 140737488355328;
   KAlign (EVar 2) 32;
   KRange (EVar 50) 7036928 140737488355072;
   KWord (SA (EVar 2) (-176)) 8 (EAlu Instr.ALU_ADD (EVar 50) (ELit (32)));
   KRange (EVar 34) 0 18446744073709551614].
Definition ss0 : sym_state := SS 868220 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=3?54#=3?90#<799<#5=#<799<,20##=3?0<+$2->0$3$4$5$6$7$8+$2->0+$32#20+$2-88+$32#20+$32#60#1$?$10$11$12#12$14+$32#60$16$17+$32#20#12^#?#???????????????#1$1<$1=$1>$1?,,5'$2#7???7?8010>0#800000000000&$2#20'$32#6;6000#7?????????00!$2-;0,8+$32#20'$22#^#?#??????????????>,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 817564 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868220 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868220 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwH1f1d.

Module LibSegNa_qtwR0a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [868536].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020; 868432; 868536] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11#7???8000$13$2=$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?8010>0#800000000000&$2#20!$2-<0,8+&6$32#3#7???8000!$2-<8,8$32!$2-=0,8$32'$2=#6;6000#7?????????>8&$2=#8)##7???7000#100000001000$2=##18#&6$2=#3#7???8000#1#&6+$2=#10#3#7???8000#1#&6+$2=#8#3#7???8000#1!$2=#,1$2?'$2?##??'&9$2?#1#1#1!$2=#8,8$28!$2=#10,8$29'$28#1#1'$29#1000#7?????????>0"%pstring).
Definition ss0 : sym_state := SS 868288 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#=4050#=40;8#=40;8#5=#=40;8,20#$1+$2->0$3$4$5$6$7$8+$2->0$29+$29#1$29$=$>$?$10$11#7???8000+&6$32#3#7???8000$2=$15$32$32$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?8010>0#800000000000&$2#20!$2-<0,8+&6$32#3#7???8000!$2-<8,8$32!$2-=0,8$32'$2=#6;6000#7?????????>8&$2=#8)##7???7000#100000001000$2=##18#&6$2=#3#7???8000#1#&6+$2=#10#3#7???8000#1#&6+$2=#8#3#7???8000#1!$2=#,1$2?'$2?##??'&9$2?#1#1#1!$2=#8,8$28!$2=#10,8$29'$28#1#1'$29#1000#7?????????>0,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 868536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 868288 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 868288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwR0a.

End BndP_Na_102.
