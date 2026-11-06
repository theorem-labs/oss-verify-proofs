(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_002 BndT_Na_000. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_048.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_002 BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_048 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_66fe992ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDl3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_c5da152ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doDs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEb3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_119fc32ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doEc3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_9596422ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doFa3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_81a7872ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGa3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_9b518c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048>LibSegNa_doGb23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_doGc3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_8086792ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048<LibSegNa_dpA3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_ac7afc2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_048=LibSegNa_dpA43kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_doDl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_66fe99.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_66fe99.IT.
Definition ENDS : list Z := [1308256].
Definition STOPS1 : list Z := [1308256] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#15;5:0$=$>$?$10$11##11#15;5:0#1?8=1#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#70%#10000#158000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-70#70$21#+$22#1!##15;5<0,8+$2#280!##15;5<8,8+$2#241!##15;5>8,8#13?624!##6;3;40,8$28"%pstring).
Definition ss0 : sym_state := SS 1315456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-112), ELit 112)].
Definition F0L : list SR.region := [(EVar 2, (-112), 112)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#13?660#13?660#5=#13?660,20##141284+$2-70$3$4$5#13?624$7$22#15;5:0$28$21$22$=$>$?$10$11##11#15;5:0#6;3;40#$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-48,8$28!$2-40,8#!$2-38,8#1?8=1!$2-30,8#15;5:0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#141284'$2#7???7?811000#800000000000&$2#10($2-70#70,$2-70#28%#10000#158000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-70#70$21#+$22#1!##15;5<0,8+$2#280!##15;5<8,8+$2#241!##15;5>8,8#13?624!##6;3;40,8$28,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1308256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_66fe99.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1315456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_66fe99.IT BndT_Na_001.SegItab_Na_66fe99.IT_sound BF NX0 BR XSTEP F0 PSS plan 1315456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doDl.

Module LibSegNa_doDs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_c5da15.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_c5da15.IT.
Definition ENDS : list Z := [519096].
Definition STOPS1 : list Z := [519096] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21$22#15;5:0$=$>$?$10$11##11#15;5:0#1?8=1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#40%#10000#158000'$21#7???7?811000#7?????????>?'$22##3?)$2-40#40$21#+$22#1!##15;5<0,8+$2#280!##15;5<8,8+$2#241!##15;630,4#????????"%pstring).
Definition ss0 : sym_state := SS 1315456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-64), 64)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;8#7>;;8#5=#7>;;8,20##140120+$2-40$3$4$5$6$7#15;5:0$22+$2#241$21$22$=$>$?$10$11$21##15;5:0#1?8=1$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-38,8#1?8=1!$2-30,8#15;5:0!$2-28,8#11!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#141284'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#8%#10000#158000'$21#7???7?811000#7?????????>?'$22##3?)$2-40#40$21#+$22#1!##15;5<0,8+$2#280!##15;5<8,8+$2#241!##15;630,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 519096 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_c5da15.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1315456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_c5da15.IT BndT_Na_002.SegItab_Na_c5da15.IT_sound BF NX0 BR XSTEP F0 PSS plan 1315456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doDs.

Module LibSegNa_doEa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_c5da15.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_c5da15.IT.
Definition ENDS : list Z := [519096].
Definition STOPS1 : list Z := [519096] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1422752; (EVar 34); EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; (EVar 34); EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#50%#10000#158000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#50$21#+$22#1(##15;5<8#8!##15;5<8,8+$2#281!$2#38,8#141284!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#11!$2#10,8#15;5:0!$2#8,8#1?8=1!##15;5:0,1#5!##15;5<0,8+$2#2<0!##15;630,4#????????"%pstring).
Definition ss0 : sym_state := SS 1311008 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 80); (ELit 0, (1422792), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 80); (ELit 0, (1422792), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;8#7>;;8#5=#7>;;8,20##140120$2$3$4$5$6$7#15;5:0#1++$2$22#281#1?8=1#1$=$>$?$10$11#1?8=1##15;5:0#1?8=2#1#1?8=1$18$19#1$1;$1<$1=$1>$1?,,14!$2#8,8#1?8=2!$2#10,8#15;5:0!$2#18,8+$22#11!$2#20,8+@-1$22#7?????>>!$2#28,8#7???????!$2#30,8#25!$2#38,8#140864!##15;5<8,8++$2$22#281'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#18%#10000#158000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#50$21#+$22#1(##15;5<8#8!##15;5:0,1#5!##15;5<0,8+$2#2<0!##15;630,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 519096 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_c5da15.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1311008 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_c5da15.IT BndT_Na_002.SegItab_Na_c5da15.IT_sound BF NX0 BR XSTEP F0 PSS plan 1311008 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doEa.

Module LibSegNa_doEb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_66fe99.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_66fe99.IT.
Definition ENDS : list Z := [1308256].
Definition STOPS1 : list Z := [1308256] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1422752; ELit 63; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; ELit 63; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#70%#10000#158000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-30#70$21#+$22#1(##15;5<8#8!##15;5<8,8+$2#281!$2#38,8#141284!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#11!$2#10,8#15;5:0!$2#8,8#1?8=1!##15;5:0,1#5!##15;5<0,8+$2#2<0!##15;5>8,8#13?624!##6;3;40,8$28"%pstring).
Definition ss0 : sym_state := SS 1311008 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-48), ELit 112); (ELit 0, (1422792), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-48), 112); (ELit 0, (1422792), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#13?660#13?660#5=#13?660,20##140864+$2-30$3$4$5#13?624$7#1#15;5:0$28#1?8=1#1$=$>$?$10$11#7?????:?#50#15;5:0#6;3;40#1#1?8=1$18$19#1$1;$1<$1=$1>$1?,,17!$2-8,8$28!$2#,8#1!$2#8,8#1?8=2!$2#10,8#15;5:0!$2#18,8#50!$2#20,8#7?????:?!$2#28,8#7???????!$2#30,8#25!$2#38,8#140864!##15;5<8,8+$2#2<0'$2#7???7?811000#800000000000&$2#10($2-30#70,$2-30#28%#10000#158000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-30#70$21#+$22#1(##15;5<8#8!##15;5:0,1#5!##15;5<0,8+$2#2<0!##15;5>8,8#13?624!##6;3;40,8$28,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1308256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_66fe99.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1311008 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_66fe99.IT BndT_Na_001.SegItab_Na_66fe99.IT_sound BF NX0 BR XSTEP F0 PSS plan 1311008 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doEb.

Module LibSegNa_doEc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_119fc3.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_119fc3.IT.
Definition ENDS : list Z := [1308256].
Definition STOPS1 : list Z := [1308256] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; (EVar 34); ELit 1422752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 7027520; EVar 122; EVar 123; ELit 0; EVar 125; (EVar 34); EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#:?0%#10000#158000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???;?18,8#(##15;5<0#8(##15;5<8#8(##15;5=8#8!##15;5?8,8+$2#2:0!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#141284!$2#60,8#25!$2#58,8#7???????!$2#50,8#!$2#48,8#11!$2#40,8#15;5:0!$2#38,8#1?8=1!$2#30,8#!##15;5:0,1#5!##15;630,4#????????!##160759,1#1!##15?:78,8#7???8000!##158=:0,8#148=68!$2#=0,8#6;3;40!$2#220,8$28!$2#288,8#140674!$2#280,8#15;5:0!$2#278,8#1?8;>!$2#270,8#6;3;40!$2#268,8#1!$2#260,8#6;4318!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##15;5>8,8#13?624"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2112), ELit 2800); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2112), 2800); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#13?660#13?660#5=#13?660,20##140694+$2#220$3$4#2$6$7##15;5:0$28###13?624##1#1#:#6;3;40#1#6;4318#6;3;40$16$17$18$19$1:$1;$1<$1=$1>$1?,,3?!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#6;4318!$2#268,8#1!$2#270,8#6;3;40!$2#278,8+$22#12!$2#280,8#15;5:0!$2#288,8#140694!##15;5<8,8+$2#2:1!$2#2:0,1#:!$2-20,8#!$2-18,8#1?8=1!$2-10,8#1!$2-8,8#1?8=2!$2#,8#15;5:0!$2#8,8#!$2#10,8#1?8=1!$2#18,8#1!$2#20,8#15;5:0!$2#28,8#140120!$2#38,8#1?8=2!$2#40,8#15;5:0!$2#48,8+$22#11!$2#50,8+@-1$22#7?????>>!$2#58,8#7???????!$2#60,8#25!$2#68,8#140864!##15;5=8,8+$2#2:0!##15;5<0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-840#:?0,$2-840#820,$2#30#8,$2#70#1=8,$2#290#10,$2#2:1#?%#10000#158000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-840#:?0$21#+$22#1#&6$2#3#7???8046#18!##7???;?18,8#(##15;5<0#8(##15;5<8#8(##15;5=8#8!##15;5?8,8+$2#2:0!##15;600,8#50!##6;3;40,8$28!$2#30,8#!##15;5:0,1#5!##15;630,4#????????!##160759,1#1!##15?:78,8#7???8000!##158=:0,8#148=68!$2#=0,8#6;3;40!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##15;5>8,8#13?624,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1308256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_119fc3.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_119fc3.IT BndT_Na_000.SegItab_Na_119fc3.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doEc.

Module LibSegNa_doFa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_959642.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_959642.IT.
Definition ENDS : list Z := [1308256].
Definition STOPS1 : list Z := [1308256] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1422752; ELit 1; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; ELit 1; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#270%#10000#158000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#270$21#+$22#1(##15;5<8#8!##15;5<8,8++$2$22#281!$2#38,8#140864!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7?????>>$22!$2#18,8+$22#11!$2#10,8#15;5:0!$2#8,8#1?8=2!$2#:0,8#6;3;40!##6;3;40,8$28!$2#1?0,8$28!$2#258,8#140674!$2#250,8#15;5:0!$2#248,8#1?8;>!$2#240,8#6;3;40!$2#238,8#1!$2#230,8#6;4318!$2#228,8#5!$2#220,8$16!$2#218,8$17!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##15;5>8,8#13?624"%pstring).
Definition ss0 : sym_state := SS 1311008 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 624); (ELit 0, (1422792), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 624); (ELit 0, (1422792), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#13?660#13?660#5=#13?660,20##140694+$2#1?0$3$4$5$6$7##15;5:0$28###13?624$>$?$10$11#6;3;40#1#6;4318#6;3;40$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$2#218,8$28!$2#220,8$16!$2#228,8#!$2#230,8#6;4318!$2#238,8#1!$2#240,8#6;3;40!$2#248,8+$22#12!$2#250,8#15;5:0!$2#258,8#140694!##15;5<8,8++$2$22#282'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#228%#10000#158000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#270$21#+$22#1(##15;5<8#8!$2#38,8#140864!$2#30,8#25!$2#28,8#7???????!$2#20,8&1#7?????>>$22!$2#18,8+$22#11!$2#10,8#15;5:0!$2#8,8#1?8=2!$2#:0,8#6;3;40!##6;3;40,8$28!$2#1?0,8$28!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##15;5>8,8#13?624,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1308256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_959642.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1311008 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_959642.IT BndT_Na_002.SegItab_Na_959642.IT_sound BF NX0 BR XSTEP F0 PSS plan 1311008 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doFa.

Module LibSegNa_doGa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_81a787.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_81a787.IT.
Definition ENDS : list Z := [1277128].
Definition STOPS1 : list Z := [1277128] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##15;5?8,8+$2#80!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8+$22#12!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!##15;5:0,4#5!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8;>!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1422752), ELit 4); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8); (ELit 0, (1422840), ELit 8); (ELit 0, (1422848), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1422752), 4); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8); (ELit 0, (1422840), 8); (ELit 0, (1422848), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#137<<8#137<<8#5=#137<<8,20##:><;<+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##15;5:0,4#5!##15;600,8#!##15;5?8,8#6;4318!##15;5=8,8#!##15;5<8,8#!##15;5<0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22##3>)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8+$22#12!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8;>!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1277128 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_81a787.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_81a787.IT BndT_Na_001.SegItab_Na_81a787.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doGa.

Module LibSegNa_doGb1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9b518c.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9b518c.IT.
Definition ENDS : list Z := [1308256].
Definition STOPS1 : list Z := [1308256] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1; ELit 1422752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; ELit 7027520; EVar 122; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#2:0%#10000#158000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#2:0$21#+$22#1(##15;5<0#8(##15;5<8#8(##15;5=8#8!##15;5?8,8+$2#2:0!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#140864!$2#60,8#25!$2#58,8#7???????!$2#50,8#7?????:?!$2#48,8#50!$2#40,8#15;5:0!$2#38,8#1?8=2!$2#30,8#1!$2#=0,8#6;3;40!$2#220,8$28!$2#288,8#140674!$2#280,8#15;5:0!$2#278,8#1?8;>!$2#270,8#6;3;40!$2#268,8#1!$2#260,8#6;4318!$2#258,8#5!$2#250,8$16!$2#248,8$17!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##15;5>8,8#13?624"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 672); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 672); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#13?660#13?660#5=#13?660,20##140694+$2#220$3$4$5$6$7##15;5:0$28###13?624$>$?$10$11#6;3;40#1#6;4318#6;3;40$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$2#248,8$28!$2#250,8$16!$2#258,8#!$2#260,8#6;4318!$2#268,8#1!$2#270,8#6;3;40!$2#278,8#51!$2#280,8#15;5:0!$2#288,8#140694!##15;5=8,8+$2#2:0!##15;5<8,8+$2#2:0!##15;5<0,8+$2#2?0'$2#7???7?811000#800000000000&$2#10($2-10#2:0,$2-10#258%#10000#158000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#2:0$21#+$22#1(##15;5<0#8(##15;5<8#8(##15;5=8#8!##15;5?8,8+$2#2:0!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#140864!$2#60,8#25!$2#58,8#7???????!$2#50,8#7?????:?!$2#48,8#50!$2#40,8#15;5:0!$2#38,8#1?8=2!$2#30,8#1!$2#=0,8#6;3;40!$2#220,8$28!$2#240,8$18!$2#238,8$19!$2#230,8$1:!$2#228,8$1;!##15;5>8,8#13?624,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1308256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9b518c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9b518c.IT BndT_Na_002.SegItab_Na_9b518c.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doGb1.

Module LibSegNa_doGb2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_81a787.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_81a787.IT.
Definition ENDS : list Z := [1277128].
Definition STOPS1 : list Z := [1277128] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##15;5?8,8+$2#80!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8#51!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!##15;5:0,4#5!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8;>!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1422752), ELit 4); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8); (ELit 0, (1422840), ELit 8); (ELit 0, (1422848), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1422752), 4); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8); (ELit 0, (1422840), 8); (ELit 0, (1422848), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#137<<8#137<<8#5=#137<<8,20##:><;<+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##15;5:0,4#5!##15;600,8#!##15;5?8,8#6;4318!##15;5=8,8#!##15;5<8,8#!##15;5<0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22#3?#3?)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8#51!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8;>!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1277128 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_81a787.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_81a787.IT BndT_Na_001.SegItab_Na_81a787.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doGb2.

Module LibSegNa_doGc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_81a787.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_81a787.IT.
Definition ENDS : list Z := [1277128].
Definition STOPS1 : list Z := [1277128] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##15;5?8,8+$2#80!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8+$22#12!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!##15;5:0,4#5!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8;>!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1422752), ELit 4); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8); (ELit 0, (1422840), ELit 8); (ELit 0, (1422848), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1422752), 4); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8); (ELit 0, (1422840), 8); (ELit 0, (1422848), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#137<<8#137<<8#5=#137<<8,20##:><;<+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##15;5:0,4#5!##15;600,8#!##15;5?8,8#6;4318!##15;5=8,8#!##15;5<8,8#!##15;5<0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22#40#1????)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8+$22#12!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8;>!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1277128 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_81a787.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_81a787.IT BndT_Na_001.SegItab_Na_81a787.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_doGc.

Module LibSegNa_dpA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_808679.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_808679.IT.
Definition ENDS : list Z := [1311596].
Definition STOPS1 : list Z := [1311596] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:>><0$2$3$4$5$6$7$8$9#15186+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;698#8(##15;6:0#8(##15;6;0#8(##15;6;8#8(##15;6<8#8(##15;6=8#8(##15;718#4(##6;4320#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;690,4#5!##15;6?0,8#400!##15;6;0,8#!##15;718,4#!##15;6>8,8#6;4320!##15;720,4#:!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<!##15;6=8,8#140310!##15;708,4#1"%pstring).
Definition ss0 : sym_state := SS 434900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1422992), ELit 4); (ELit 0, (1423000), ELit 8); (ELit 0, (1423008), ELit 8); (ELit 0, (1423024), ELit 8); (ELit 0, (1423032), ELit 8); (ELit 0, (1423048), ELit 8); (ELit 0, (1423064), ELit 8); (ELit 0, (1423128), ELit 4); (ELit 0, (7029536), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1422992), 4); (ELit 0, (1423000), 8); (ELit 0, (1423008), 8); (ELit 0, (1423024), 8); (ELit 0, (1423032), 8); (ELit 0, (1423048), 8); (ELit 0, (1423064), 8); (ELit 0, (1423128), 4); (ELit 0, (7029536), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14036<#14036<#5=#14036<,20##140104+$2-450$3$4#$6$7#6;3;40#1#1#5413+$2-450#15188#5413#1#15;690#1=#15188#1##15189#1#15188#1##1#1$1<$1=$1>$1?,,<2!##15;6=8,8#13?624!$2-448,8$28!$2-440,8#15;690!$2-438,8#140104!$2-428,8#15189!$2-420,8#15;690!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#140864!##15;6;8,8#6;4321!$2-480,8#1!$2-478,8+$2-340!$2-470,8#!$2-468,8#15188!$2-460,8#15;690!$2-458,8#!$2-450,8+$2-340!##6;4320,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10>4?!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#6;3;40!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#6;3;40!$2-1>8,8#15186!$2-1>0,8#15;690!$2-1=8,8#140674!##15;6;0,8#6;4720!##15;6:0,8#!##15;698,8#!##15;6<8,8#6;4320!##15;718,4^#?#???????????????!##15;690,4#5!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#15;690!$2-70,8#15186!$2-68,8#6>9>8!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#15186!$2-930,8+$2-60!$2-928,8#6>23<!$2-918,8+$2-=8!$2-910,8#2105>!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#15186!$2-38,8#6=>78!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14:00!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:>><0'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;698#8(##15;6:0#8(##15;6;0#8(##15;6;8#8(##15;6<8#8(##15;6=8#8(##15;718#4(##6;4320#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;6?0,8#400!##15;6>8,8#6;4320!##15;720,4#:!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<!##15;708,4#1,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1311596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_808679.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 434900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_808679.IT BndT_Na_001.SegItab_Na_808679.IT_sound BF NX0 BR XSTEP F0 PSS plan 434900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpA.

Module LibSegNa_dpA2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_ac7afc.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_ac7afc.IT.
Definition ENDS : list Z := [716480].
Definition STOPS1 : list Z := [716480] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:>><0$2$3$4$5$6$7$8$9#15186+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;6;8#8(##6;4320#1(##6;4321#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;690,4#5!##15;6?0,8#400!##15;6;0,8#6;4720!##15;6;8,8#6;4320!##15;720,4#????????!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<"%pstring).
Definition ss0 : sym_state := SS 434900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1422992), ELit 4); (ELit 0, (1423032), ELit 8); (ELit 0, (7029536), ELit 1); (ELit 0, (7029537), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1422992), 4); (ELit 0, (1423032), 8); (ELit 0, (7029536), 1); (ELit 0, (7029537), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>><0#:>><0#5=#:>><0,20##:>><0$2$3$4#$6$7$8$9#2$28$28#6;4321##1##$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;7!##15;690,4#5!##15;6;8,8#6;4322!##6;4321,1#:!$2-480,8#1!$2-478,8#15188!$2-470,8#1!$2-468,8#15189!$2-460,8#15;690!$2-458,8#!$2-450,8#15188!$2-448,8#1!$2-440,8#15;690!$2-438,8#140120!$2-428,8#15189!$2-420,8#15;690!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#140864!##6;4320,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10>4?!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#6;3;40!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#6;3;40!$2-1>8,8#15186!$2-1>0,8#15;690!$2-1=8,8#140674!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#15;690!$2-70,8#15186!$2-68,8#6>9>8!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#15186!$2-930,8+$2-60!$2-928,8#6>23<!$2-918,8+$2-=8!$2-910,8#2105>!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#15186!$2-38,8#6=>78!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14:00!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:>><0'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;6;8#8(##6;4320#1(##6;4321#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;6?0,8#400!##15;6;0,8#6;4720!##15;720,4#????????!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 716480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_ac7afc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 434900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_ac7afc.IT BndT_Na_002.SegItab_Na_ac7afc.IT_sound BF NX0 BR XSTEP F0 PSS plan 434900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpA2.

Module LibSegNa_dpA3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_ac7afc.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_ac7afc.IT.
Definition ENDS : list Z := [716480].
Definition STOPS1 : list Z := [716480] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:>><0$2$3$4$5$6$7$8$9#15186+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;6;8#8(##6;4322#1(##6;4323#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;690,4#5!##15;6?0,8#400!##15;6;0,8#6;4720!##15;6;8,8#6;4322!##15;720,4#????????!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<"%pstring).
Definition ss0 : sym_state := SS 434900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1422992), ELit 4); (ELit 0, (1423032), ELit 8); (ELit 0, (7029538), ELit 1); (ELit 0, (7029539), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1422992), 4); (ELit 0, (1423032), 8); (ELit 0, (7029538), 1); (ELit 0, (7029539), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>><0#:>><0#5=#:>><0,20##:>><0$2$3$4#$6$7$8$9#2$28$28#6;4323##3##$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;7!##15;690,4#5!##15;6;8,8#6;4324!##6;4323,1#:!$2-480,8#1!$2-478,8#15188!$2-470,8#1!$2-468,8#15189!$2-460,8#15;690!$2-458,8#!$2-450,8#15188!$2-448,8#1!$2-440,8#15;690!$2-438,8#140120!$2-428,8#15189!$2-420,8#15;690!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#140864!##6;4322,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10>4?!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#6;3;40!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#6;3;40!$2-1>8,8#15186!$2-1>0,8#15;690!$2-1=8,8#140674!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#15;690!$2-70,8#15186!$2-68,8#6>9>8!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#15186!$2-930,8+$2-60!$2-928,8#6>23<!$2-918,8+$2-=8!$2-910,8#2105>!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#15186!$2-38,8#6=>78!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14:00!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:>><0'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;6;8#8(##6;4322#1(##6;4323#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;6?0,8#400!##15;6;0,8#6;4720!##15;720,4#????????!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 716480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_ac7afc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 434900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_ac7afc.IT BndT_Na_002.SegItab_Na_ac7afc.IT_sound BF NX0 BR XSTEP F0 PSS plan 434900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpA3.

Module LibSegNa_dpA4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_ac7afc.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_ac7afc.IT.
Definition ENDS : list Z := [716480].
Definition STOPS1 : list Z := [716480] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##:>><0$2$3$4$5$6$7$8$9#15186+$2#18$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#<:0%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;6;8#8(##6;4324#1(##6;4325#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;690,4#5!##15;6?0,8#400!##15;6;0,8#6;4720!##15;6;8,8#6;4324!##15;720,4#????????!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<"%pstring).
Definition ss0 : sym_state := SS 434900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-3232), ELit 3232); (ELit 0, (1422992), ELit 4); (ELit 0, (1423032), ELit 8); (ELit 0, (7029540), ELit 1); (ELit 0, (7029541), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-3232), 3232); (ELit 0, (1422992), 4); (ELit 0, (1423032), 8); (ELit 0, (7029540), 1); (ELit 0, (7029541), 1)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:>><0#:>><0#5=#:>><0,20##:>><0$2$3$4#$6$7$8$9#2$28$28#6;4325##1##$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;7!##15;690,4#5!##15;6;8,8#6;4326!##6;4325,1#:!$2-480,8#1!$2-478,8#15188!$2-470,8#1!$2-468,8#15189!$2-460,8#15;690!$2-458,8#!$2-450,8#15188!$2-448,8#1!$2-440,8#15;690!$2-438,8#140120!$2-428,8#15189!$2-420,8#15;690!$2-418,8#1!$2-410,8#7??????>!$2-408,8#7???????!$2-400,8#25!$2-3?8,8#140864!##6;4324,1#30!$2-340,1#30!$2-430,8#!$2-3>8,8#!$2-3=0,8#1!$2-3>0,8#!$2-3?0,8#10>4?!$2-3=8,8#!$2-380,8#!$2-1=0,8+$2#20!$2-3<8,8^#?#???????<<<<<<<=!$2-3<0,8^#?#??????????>????!$2-388,8#<<<<<<<!$2-3:0,8#12889!$2-240,8$28!$2-390,8#6;3;40!$2-398,8#!$2-3:8,8+$2-1=0!$2-3;8,8+$2-170!$2-3;0,8+$2-<8!$2-238,8$1;!$2-230,8$1:!$2-228,8$19!$2-220,8$18!$2-218,8$17!$2-210,8$16!$2-208,8#5!$2-200,8#!$2-1?8,8#1!$2-1?0,8#6;3;40!$2-1>8,8#15186!$2-1>0,8#15;690!$2-1=8,8#140674!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,8#!$2-:8,8#!$2-1<8,8+$2#18!$2-:0,8$28!$2-98,8$15!$2-90,8$14!$2-88,8$13!$2-80,8+$2#18!$2-78,8#15;690!$2-70,8#15186!$2-68,8#6>9>8!$2-900,8^#?#???????????????!$2-8>1,1#!$2-8>2,1#!$2-8>3,1#!$2-8>4,1#!$2-8>5,1#!$2-8>6,1#!$2-8>7,1#!$2-8>8,1#!$2-8>9,1#!$2-8>:,1#!$2-8>;,1#!$2-8><,1#!$2-8>=,1#!$2-8>>,1#!$2-8>?,1#!$2-8?0,1#!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?4,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-8?8,1#!$2-901,1#!$2-902,1#!$2-903,1#!$2-904,1#!$2-905,1#!$2-906,1#!$2-907,1#!$2-908,1#!$2-940,8#:!$2-938,8#15186!$2-930,8+$2-60!$2-928,8#6>23<!$2-918,8+$2-=8!$2-910,8#2105>!$2-60,8+$2#18!$2-58,8+$2#18!$2-50,8$12!$2-48,8+$2#18!$2-40,8#15186!$2-38,8#6=>78!$2-8=0,8^#?#???????????????!$2-8;1,1#!$2-8;2,1#!$2-8;3,1#!$2-8;4,1#!$2-8;5,1#!$2-8;6,1#!$2-8;7,1#!$2-8;8,1#!$2-8;9,1#!$2-8;:,1#!$2-8;;,1#!$2-8;<,1#!$2-8;=,1#!$2-8;>,1#!$2-8;?,1#!$2-8<0,1#!$2-8<1,1#!$2-8<2,1#!$2-8<3,1#!$2-8<4,1#!$2-8<5,1#!$2-8<6,1#!$2-8<7,1#!$2-8<8,1#!$2-8=1,1#!$2-8=2,1#!$2-8=3,1#!$2-8=4,1#!$2-8=5,1#!$2-8=6,1#!$2-8=7,1#!$2-8=8,1#!$2-8>0,8#14:00!$2-28,8+$2#18!$2-20,8+$2#18!$2-18,8$9!$2-10,8$8!$2-8,8#:>><0'$2#7???7?811000#800000000000&$2#10($2-<:0#<:0,$2-<:0#360,$2-920#8,$2-8;0#430,$2-378#38,$2-33?#??,$2-1<0#?8,$2-30#8%#10000#158000#&6$2#3#7???7?8<#18!##7???::30,8#!##800<>860,8#(##15;690#4(##15;6;8#8(##6;4324#1(##6;4325#1!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000!##158<20,8#146850!##158<28,8#14056<!##6;3;40,8$28!##15;71<,4#????????!##15;6?0,8#400!##15;6;0,8#6;4720!##15;720,4#????????!##160759,1#1!##158=:0,8#148=68!$2#18,4#!##158=:8,8#14916<,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 716480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_ac7afc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 434900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_ac7afc.IT BndT_Na_002.SegItab_Na_ac7afc.IT_sound BF NX0 BR XSTEP F0 PSS plan 434900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpA4.

End BndP_Na_048.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002 BndT_Na_001 BndT_Na_003 BndT_Na_000.
Module BndP_Na_050.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_002 BndT_Na_001 BndT_Na_003 BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_050 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_9f5b812ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_22BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_25XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_23kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050?LibSegNa_dpXd_43kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_572cde2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXe3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_dpXm3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_fff2e72ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drA3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_5bdf212ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drB3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0a84702ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_drD3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_c5da152ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drDs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drEa3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_9596422ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drFa3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_81a7872ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050=LibSegNa_drGa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0219;BndP_Na_050<LibSegNa_duB3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_dpXd_2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9f5b81.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9f5b81.IT.
Definition ENDS : list Z := [1276376].
Definition STOPS1 : list Z := [1276376] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422992; EVar 110; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000(##15;6;0#8(##15;6;8#8(##15;6<8#8!##15;6>8,8#6;4320!##15;6?0,8#400!##6;3;40,8$28!$2#28,8$28!$2#68,8#13?<;4!$2#60,8#15;690!$2#58,8$9!$2#50,8$12!$2#48,8$13!$2#40,8$14!$2#38,8$15!$2#30,8$16!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#!$2#78,8#137=34!$2#70,8$:"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1423024), ELit 8); (ELit 0, (1423032), ELit 8); (ELit 0, (1423048), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1423024), 8); (ELit 0, (1423032), 8); (ELit 0, (1423048), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#1379=8#1379=8#5=#1379=8,20##137=3<+$2#80$3$4$5$6$7$:$9$:$:$28$=$>$?$10#5>$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!##15;6<8,8#6;4320!##15;6;8,8#6;4320!##15;6;0,8#6;4720'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000(##15;6;0#8(##15;6;8#8(##15;6<8#8!##15;6>8,8#6;4320!##15;6?0,8#400!##6;3;40,8$28!$2#28,8$28!$2#68,8#13?<;4!$2#60,8#15;690!$2#58,8$9!$2#50,8$12!$2#48,8$13!$2#40,8$14!$2#38,8$15!$2#30,8$16!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#!$2#78,8#137=34!$2#70,8$:,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1276376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9f5b81.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9f5b81.IT BndT_Na_002.SegItab_Na_9f5b81.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpXd_2.

Module LibSegNa_dpXd_3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9f5b81.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9f5b81.IT.
Definition ENDS : list Z := [1276376].
Definition STOPS1 : list Z := [1276376] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422992; EVar 110; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000(##15;6;0#8(##15;6;8#8(##15;6<8#8!##15;6>8,8#6;4320!##15;6?0,8#400!##6;3;40,8$28!$2#28,8$28!$2#68,8#13?<;4!$2#60,8#15;690!$2#58,8$9!$2#50,8$12!$2#48,8$13!$2#40,8$14!$2#38,8$15!$2#30,8$16!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#!$2#78,8#137=34!$2#70,8$:"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1423024), ELit 8); (ELit 0, (1423032), ELit 8); (ELit 0, (1423048), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1423024), 8); (ELit 0, (1423032), 8); (ELit 0, (1423048), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#1379=8#1379=8#5=#1379=8,20##137=3<+$2#80$3$4$5$6$7$:$9$:$:$28$=$>$?$10#5>$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!##15;6<8,8#6;4320!##15;6;8,8#6;4320!##15;6;0,8#6;4720'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000(##15;6;0#8(##15;6;8#8(##15;6<8#8!##15;6>8,8#6;4320!##15;6?0,8#400!##6;3;40,8$28!$2#28,8$28!$2#68,8#13?<;4!$2#60,8#15;690!$2#58,8$9!$2#50,8$12!$2#48,8$13!$2#40,8$14!$2#38,8$15!$2#30,8$16!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#!$2#78,8#137=34!$2#70,8$:,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1276376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9f5b81.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9f5b81.IT BndT_Na_002.SegItab_Na_9f5b81.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpXd_3.

Module LibSegNa_dpXd_4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9f5b81.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9f5b81.IT.
Definition ENDS : list Z := [1276376].
Definition STOPS1 : list Z := [1276376] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422992; EVar 110; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000(##15;6;0#8(##15;6;8#8(##15;6<8#8!##15;6>8,8#6;4320!##15;6?0,8#400!##6;3;40,8$28!$2#28,8$28!$2#68,8#13?<;4!$2#60,8#15;690!$2#58,8$9!$2#50,8$12!$2#48,8$13!$2#40,8$14!$2#38,8$15!$2#30,8$16!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#!$2#78,8#137=34!$2#70,8$:"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1423024), ELit 8); (ELit 0, (1423032), ELit 8); (ELit 0, (1423048), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1423024), 8); (ELit 0, (1423032), 8); (ELit 0, (1423048), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#1379=8#1379=8#5=#1379=8,20##137=3<+$2#80$3$4$5$6$7$:$9$:$:$28$=$>$?$10#5>$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!##15;6<8,8#6;4320!##15;6;8,8#6;4320!##15;6;0,8#6;4720'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000(##15;6;0#8(##15;6;8#8(##15;6<8#8!##15;6>8,8#6;4320!##15;6?0,8#400!##6;3;40,8$28!$2#28,8$28!$2#68,8#13?<;4!$2#60,8#15;690!$2#58,8$9!$2#50,8$12!$2#48,8$13!$2#40,8$14!$2#38,8$15!$2#30,8$16!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#!$2#78,8#137=34!$2#70,8$:,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1276376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9f5b81.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9f5b81.IT BndT_Na_002.SegItab_Na_9f5b81.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpXd_4.

Module LibSegNa_dpXe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_572cde.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_572cde.IT.
Definition ENDS : list Z := [1276376].
Definition STOPS1 : list Z := [1276376] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; ELit 6896384; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",335'$2#7???7?811000#800000000000&$2#10($2-140#140,$2-140#140%#10000#158000(##15<3<0#8(##15<410#1(##15=330#8(##6;3;50#1(##6;3;58#4(##6;3;60#8(##6;3=70#4(##7???<748#1(##7???<749#1(##7???<74:#1(##7???<74;#1(##7???<74<#1(##7???<74<#4(##7???<74=#1(##7???<74>#1(##7???<74?#1(##7???<750#4(##7???<754#1(##7???<754#4(##7???<755#1(##7???<756#1(##7???<757#1(##7???<75<#1(##7???<75=#1(##7???<75>#1(##7???<75?#1(##7???<760#1(##7???<760#4(##7???<761#1(##7???<762#1(##7???<763#1(##7???<764#4(##7???<768#1(##7???<768#4(##7???<769#1(##7???<76:#1(##7???<76;#1(##7???<76<#1(##7???<76=#1(##7???<76>#1(##7???<76?#1(##7???<770#1(##7???<771#1(##7???<772#1(##7???<773#1(##7???<774#1(##7???<775#1(##7???<776#1(##7???<777#1(##7???<784#1(##7???<785#1(##7???<786#1(##7???<787#1(##7???<788#1(##7???<789#1(##7???<78:#1(##7???<78;#1(##7???<78<#1(##7???<78<#4(##7???<78=#1(##7???<78>#1(##7???<78?#1(##7???<790#4(##7???<794#4(##7???<798#4(##7???<79<#4(##7???<7:0#4(##7???<7:4#4(##7???<7:8#8(##7???<7;0#8(##7???<7;8#8(##7???<7<0#8(##7???<7<8#8(##7???<7=0#8(##7???<7=8#8(##7???<7>0#8(##7???<7>8#8(##7???<7?0#8(##7???<7?8#8(##7???<800#8(##7???<808#8(##7???<810#8(##7???<818#8(##7???<820#8(##7???<828#8(##7???<830#8(##7???<838#8(##7???<840#8(##7???<848#8(##7???<850#8(##7???<858#8(##7???<860#8(##7???<868#8(##7???<870#8(##7???<878#8(##7???<880#8(##7???<888#8(##7???<890#8(##7???<898#8(##7???<8:0#8(##7???<8:8#8(##7???<8;0#8(##7???<8;8#8(##7???<8<0#8(##7???<8<8#8(##7???<8=0#8(##7???<8=8#8(##7???<8>0#8(##7???<8>8#8(##7???<8?0#8(##7???<8?8#8(##7???<900#8(##7???<908#8(##7???<910#8(##7???<918#8(##7???<920#8(##7???<928#8(##7???<930#8(##7???<938#8(##7???<940#8(##7???<948#8(##7???<950#8(##7???<958#8(##7???<960#8(##7???<968#8(##7???<970#8(##7???<978#8(##7???<980#8(##7???<988#8(##7???<990#8(##7???<998#8(##7???<9:0#8(##7???<9:8#8(##7???<9;0#8(##7???<9;8#8(##7???<9<0#8(##7???<9<8#8(##7???<9=0#8(##7???<9=8#8(##7???<9>0#8(##7???<9>8#8(##7???<9?0#8(##7???<9?8#8(##7???<:00#8(##7???<:08#8(##7???<:10#8(##7???<:18#8(##7???<:20#8(##7???<:28#8(##7???<:30#8(##7???<:38#8(##7???<:40#8(##7???<:48#8(##7???<:50#8(##7???<:58#8(##7???<:60#8(##7???<:68#8(##7???<:70#8(##7???<:78#8(##7???<:80#8(##7???<:88#8(##7???<:90#8(##7???<:98#8(##7???<::0#8(##7???<::8#8(##7???<:;0#8(##7???<:;8#8(##7???<:<0#8(##7???<:<8#4(##7???<:<<#4(##7???<:=0#4(##7???<:=4#4(##7???<:=8#4(##7???<:=<#4(##7???<:>0#1(##7???<:>0#4(##7???<:>1#1(##7???<:>2#1(##7???<:>3#1(##7???<:>4#1(##7???<:>4#4(##7???<:>5#1(##7???<:>6#1(##7???<:>7#1(##7???<:>8#4(##7???<:><#4(##7???<:?0#4(##7???<:?4#4(##7???<:?8#4(##7???<:?<#4(##7???<;00#8(##7???<;08#8(##7???<;10#8(##7???<;18#8(##7???<;20#8(##7???<;28#8(##7???<;30#8(##7???<;38#8(##7???<;40#8(##7???<;48#8(##7???<;50#8(##7???<;58#8(##7???<;60#8(##7???<;68#8(##7???<;70#8(##7???<;78#8(##7???<;80#8(##7???<;88#8(##7???<;90#8(##7???<;98#8(##7???<;:0#8(##7???<;:8#8(##7???<;;0#8(##7???<;;8#8(##7???<;<0#8(##7???<;<8#8(##7???<;=0#8(##7???<;=8#8(##7???<;>0#8(##7???<;>8#8(##7???<;?0#8(##7???<;?8#8(##7???<<00#8(##7???<<08#8(##7???<<10#8(##7???<<18#8(##7???<<20#8(##7???<<28#8(##7???<<30#8(##7???<<38#8(##7???<<40#8(##7???<<48#8(##7???<<50#8(##7???<<58#8(##7???<<60#8(##7???<<68#8(##7???<<70#8(##7???<<74#4(##7???<<78#4(##7???<<78#8(##7???<<7<#4(##7???<<80#4(##7???<<84#4(##7???<<88#4(##7???<<8<#1(##7???<<8<#4(##7???<<8=#1(##7???<<8>#1(##7???<<8?#1(##7???<<90#1(##7???<<91#1(##7???<<92#1(##7???<<93#1(##7???<<94#1(##7???<<94#4(##7???<<95#1(##7???<<96#1(##7???<<97#1(##7???<<98#4(##7???<<9<#4(##7???<<:0#1(##7???<<:0#4(##7???<<:1#1(##7???<<:2#1(##7???<<:3#1(##7???<<:4#1(##7???<<:5#1(##7???<<:6#1(##7???<<:7#1(##7???<<:8#1(##7???<<:9#1(##7???<<::#1(##7???<<:;#1(##7???<<:<#1(##7???<<:=#1(##7???<<:>#1(##7???<<:?#1(##7???<<;0#1(##7???<<;1#1(##7???<<;2#1(##7???<<;3#1(##7???<<;4#1(##7???<<;5#1(##7???<<;6#1(##7???<<;7#1(##7???<<<<#1(##7???<<<=#1(##7???<<<>#1(##7???<<<?#1(##7???<<?<#1(##7???<<?=#1(##7???<<?>#1(##7???<<??#1(##7???<=00#1(##7???<=01#1(##7???<=02#1(##7???<=03#1(##7???<=04#1(##7???<=05#1(##7???<=06#1(##7???<=07#1(##7???<=08#1(##7???<=09#1(##7???<=0:#1(##7???<=0;#1(##7???<=0<#1(##7???<=0=#1(##7???<=0>#1(##7???<=0?#1(##7???<=10#1(##7???<=10#4(##7???<=11#1(##7???<=12#1(##7???<=13#1(##7???<=14#4(##7???<=18#1(##7???<=18#4(##7???<=19#1(##7???<=1:#1(##7???<=1;#1(##7???<=1<#1(##7???<=1<#4(##7???<=1=#1(##7???<=1>#1(##7???<=1?#1(##7???<=20#4(##7???<=24#1(##7???<=24#4(##7???<=25#1(##7???<=26#1(##7???<=27#1(##7???<=28#1(##7???<=28#4(##7???<=29#1(##7???<=2:#1(##7???<=2;#1(##7???<=2<#4(##7???<=30#1(##7???<=30#4(##7???<=31#1(##7???<=32#1(##7???<=33#1(##7???<=34#1(##7???<=34#4(##7???<=35#1(##7???<=36#1(##7???<=37#1(##7???<=38#4(##7???<=3<#1(##7???<=3<#4(##7???<=3=#1(##7???<=3>#1(##7???<=3?#1(##7???<=40#1(##7???<=40#4(##7???<=41#1(##7???<=42#1(##7???<=43#1(##7???<=44#4(##7???<=48#1(##7???<=48#4(##7???<=49#1(##7???<=4:#1(##7???<=4;#1(##7???<=4<#1(##7???<=4<#4(##7???<=4=#1(##7???<=4>#1(##7???<=4?#1(##7???<=50#4(##7???<=54#1(##7???<=54#4(##7???<=55#1(##7???<=56#1(##7???<=57#1(##7???<=58#1(##7???<=58#4(##7???<=59#1(##7???<=5:#1(##7???<=5;#1(##7???<=5<#4(##7???<=60#4(##7???<=64#1(##7???<=64#4(##7???<=65#1(##7???<=66#1(##7???<=67#1(##7???<=68#1(##7???<=69#1(##7???<=6:#1(##7???<=6;#1(##7???<=6<#1(##7???<=6=#1(##7???<=6>#1(##7???<=6?#1(##7???<=70#1(##7???<=71#1(##7???<=72#1(##7???<=73#1(##7???<=74#1(##7???<=75#1(##7???<=76#1(##7???<=77#1(##7???<=78#1(##7???<=78#4(##7???<=79#1(##7???<=7:#1(##7???<=7;#1(##7???<=7<#4(##7???<=80#1(##7???<=80#4(##7???<=81#1(##7???<=82#1(##7???<=83#1(##7???<=84#1(##7???<=84#4(##7???<=85#1(##7???<=86#1(##7???<=87#1(##7???<=88#4(##7???<=8<#1(##7???<=8<#4(##7???<=8=#1(##7???<=8>#1(##7???<=8?#1(##7???<=90#1(##7???<=90#4(##7???<=91#1(##7???<=92#1(##7???<=93#1(##7???<=94#4(##7???<=98#1(##7???<=98#4(##7???<=99#1(##7???<=9:#1(##7???<=9;#1(##7???<=9<#1(##7???<=9<#4(##7???<=9=#1(##7???<=9>#1(##7???<=9?#1(##7???<=:0#4(##7???<=:4#1(##7???<=:4#4(##7???<=:5#1(##7???<=:6#1(##7???<=:7#1(##7???<=:8#1(##7???<=:8#4(##7???<=:9#1(##7???<=::#1(##7???<=:;#1(##7???<=:<#4(##7???<=;0#1(##7???<=;0#4(##7???<=;1#1(##7???<=;2#1(##7???<=;3#1(##7???<=;4#1(##7???<=;4#4(##7???<=;5#1(##7???<=;6#1(##7???<=;7#1(##7???<=;8#4(##7???<=;<#1(##7???<=;<#4(##7???<=;=#1(##7???<=;>#1(##7???<=;?#1(##7???<=<0#1(##7???<=<1#1(##7???<=<2#1(##7???<=<3#1(##7???<=>8#1(##7???<=>9#1(##7???<=>:#1(##7???<=>;#1(##7???<=><#1(##7???<=>=#1(##7???<=>>#1(##7???<=>?#1(##7???<=?0#1(##7???<=?1#1(##7???<=?2#1(##7???<=?3#1(##7???<=?4#1(##7???<=?5#1(##7???<=?6#1(##7???<=?7#1(##7???<>04#1(##7???<>04#4(##7???<>05#1(##7???<>06#1(##7???<>07#1(##7???<>08#4(##7???<>0<#1(##7???<>0<#4(##7???<>0=#1(##7???<>0>#1(##7???<>0?#1(##7???<>10#1(##7???<>10#4(##7???<>11#1(##7???<>12#1(##7???<>13#1(##7???<>14#4(##7???<>18#4(##7???<>1<#4(##7???<>20#4(##7???<>24#4(##7???<>28#4(##7???<>28#8(##7???<>30#8(##7???<>38#4(##7???<>38#8(##7???<>3<#4(##7???<>40#4(##7???<>40#8(##7???<>44#4(##7???<>48#4(##7???<>4<#4(##7???<>50#1(##7???<>50#4(##7???<>51#1(##7???<>52#1(##7???<>53#1(##800222:4#1(##800222:4#4(##800222:5#1(##800222:6#1(##800222:7#1(##800222:8#4(##800222:<#4(##800222;0#1(##800222;0#4(##800222;1#1(##800222;2#1(##800222;3#1(##80023714#1(##80023714#4(##80023715#1(##80023716#1(##80023717#1(##80023718#4(##8002371<#4(##80023720#4(##80023724#4(##80023728#4(##8002372<#4(##80023730#8(##80023738#8(##80023740#8(##80023748#8(##80023750#8(##80023758#8(##80023760#8(##80023768#8(##80023770#8(##80023778#8(##80023780#8(##80023788#8(##80023790#8(##80023798#8(##800237:0#8(##800237:8#8(##800237;0#8(##800237;8#8(##800237<0#8(##800237<8#8(##800237=0#8(##800237=8#8(##800237>0#8(##800237>8#8(##800237?0#8(##800237?8#8(##80023800#8(##80023808#8(##80023810#8(##80023818#8(##80023820#8(##80023828#8(##80023830#8(##80023838#8(##80023840#8(##80023848#8(##80023850#8(##80023858#8(##80023858#4(##8002385<#4(##80023860#8(##80023860#4(##80023864#4(##80023868#8(##80023868#4(##8002386<#4(##80023870#1(##80023870#4(##80023871#1(##80023872#1(##80023873#1!##693:58,4$2<'$2<#1#3?????!##6;3=70,4#!##6;3=93,1#!##6;3;60,8#6;3;68!##6;3;58,4#1!##6;3;70,8#137<74!##6;3<70,8#9>48<!##6;3;54,4#!##1?1920,1#!##6;3;68,8#!##15<410,1#!##158;:8,8#158;:8!##15<3<0,8#1!##15=290,4#1!##15=330,8#!##160758,1#1!##15?:78,8#7???8000!##15;8:0,8#23:40!##15;8;0,1#20!##15?2=<,1#1!##15;8;0,8#20!##1?1620,8^#?#???????????????!##158=:8,8#14916<!##15;8=8,8^#?#???????????????!##15;8>0,8#23:60!##15;8?0,1#60!##15;8?0,8#60!##15;918,8^#?#???????????????!##15;920,8#23:>0!##15;930,1#20!##15;930,8#20!##15;958,8^#?#???????????????!##15;960,8#23;00!##15;970,1#60!##15;970,8#60!##15;998,8^#?#???????????????!##15;9:0,8#23;60!##15;9;0,1#20!##15;9;0,8#20!##15;9=8,8^#?#???????????????!##15;9>0,8#23;80!##15;9?0,1#40!##15;9?0,8#40!##15;:18,8^#?#???????????????!##15;:20,8#23<20!##15;:30,1#20!##15;:30,8#20!##15;:58,8^#?#???????????????!##15;:60,8#23<40!##15;:70,1#20!##15;:70,8#20!##15;:98,8^#?#???????????????!##15;::0,8#23<60!##15;:;0,1#<0!##15;:;0,8#1:<0!##15;:=8,8^#?#???????????????!##15;:>0,8#25720!##15;:?0,1#60!##15;:?0,8#=60!##15;;18,8^#?#???????????????!##15;;20,8#26480!##15;;30,1#20!##15;;30,8#20!##15;;58,8^#?#???????????????!##15;;60,8#264:0!##15;;70,1#80!##15;;70,8#80!##15;;98,8^#?#???????????????!##15;;:0,8#26520!##15;;;0,1#20!##15;;;0,8#20!##15;;=8,8^#?#???????????????!##15;;>0,8#26540!##15;;?0,1#20!##15;;?0,8#20!##15;<18,8^#?#???????????????!##15;<20,8#26560!##15;<30,1#20!##15;<30,8#20!##15;<58,8^#?#???????????????!##15;<60,8#26580!##15;<70,1#20!##15;<70,8#20!##15;<98,8^#?#???????????????!##15;<:0,8#265:0!##15;<;0,1#20!##15;<;0,8#20!##15;<=8,8^#?#???????????????!##15;<>0,8#26660!##15;<?0,1#20!##15;<?0,8#20!##15;=18,8^#?#???????????????!##15;=20,8#267>0!##15;=30,1#40!##15;=30,8#40!##15;=58,8^#?#???????????????!##15;=60,8#26820!##15;=70,1#40!##15;=70,8#40!##15;=98,8^#?#???????????????!##15;=:0,8#26860!##15;=;0,1#20!##15;=;0,8#20!##15;==8,8^#?#???????????????!##15;=>0,8#26880!##15;=?0,1#60!##15;=?0,8#60!##15;>18,8^#?#???????????????!##15;>20,8#268>0!##15;>30,1#60!##15;>30,8#60!##15;>58,8^#?#???????????????!##15;>60,8#26940!##15;>70,1#60!##15;>70,8#60!##15;>98,8^#?#???????????????!##15;>:0,8#269:0!##15;>;0,1#60!##15;>;0,8#60!##15;>=8,8^#?#???????????????!##15;>>0,8#26:00!##15;>?0,1#60!##15;>?0,8#60!##15;?18,8^#?#???????????????!##15;?20,8#26:60!##15;?30,1#60!##15;?30,8#60!##15;?58,8^#?#???????????????!##15;?60,8#26:<0!##15;?70,1#80!##15;?70,8#80!##15;?98,8^#?#???????????????!##15;?:0,8#26;40!##15;?;0,1#40!##15;?;0,8#40!##15;?=8,8^#?#???????????????!##15;?>0,8#26;80!##15;??0,1#40!##15;??0,8#40!##15<018,8^#?#???????????????!##15<020,8#26;<0!##15<030,1#60!##15<030,8#60!##15<058,8^#?#???????????????!##15<060,8#26<20!##15<070,1#60!##15<070,8#60!##15<098,8^#?#???????????????!##15<0:0,8#26<80!##15<0;0,1#60!##15<0;0,8#60!##15<0=8,8^#?#???????????????!##15<0>0,8#26<>0!##15<0?0,1#60!##15<0?0,8#60!##15<118,8^#?#???????????????!##15<120,8#26=40!##15<130,1#60!##15<130,8#60!##15<158,8^#?#???????????????!##15<160,8#26=:0!##15<170,1#60!##15<170,8#60!##15<198,8^#?#???????????????!##15<1:0,8#26>00!##15<1;0,1#20!##15<1;0,8#20!##15<1=8,8^#?#???????????????!##15<1>0,8#26?40!##15<1?0,1#20!##15<1?0,8#20!##15<218,8^#?#???????????????!##15<220,8#26?60!##15<230,1#20!##15<230,8#20!##15<258,8^#?#???????????????!##15<260,8#26?80!##15<270,1#20!##15<270,8#20!##15<298,8^#?#???????????????!##15<2:0,8#26?:0!##15<2;0,1#20!##15<2;0,8#20!##15<2=8,8^#?#???????????????!##15<2>0,8#27020!##15<2?0,1#60!##15<2?0,8#60!##15<318,8^#?#???????????????!##15<320,8#27080!##15<330,1#20!##15<330,8#220!##15<358,8^#?#???????????????!##15<360,8#151520!##15<370,1#80!##15<370,8#80!##15<398,8^#?#???????????????!##6;4308,8#!##15;868,8#15;780!##15;80<,4#????????!##15;7:8,8#!##15;7;8,8#!##15;788,8#!##15;790,8#!##15;778,8#15;690!##15;71<,4#????????!##15;6;8,8#!##15;6<8,8#!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#"%pstring).
Definition ss0 : sym_state := SS 1277128 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",259$2-140#140##15<3<0#8##15<410#1##15=330#8##6;3;50#1##6;3;58#4##6;3;60#8##6;3=70#4##7???<748#1##7???<749#1##7???<74:#1##7???<74;#1##7???<74<#1##7???<74<#4##7???<74=#1##7???<74>#1##7???<74?#1##7???<750#4##7???<754#1##7???<754#4##7???<755#1##7???<756#1##7???<757#1##7???<75<#1##7???<75=#1##7???<75>#1##7???<75?#1##7???<760#1##7???<760#4##7???<761#1##7???<762#1##7???<763#1##7???<764#4##7???<768#1##7???<768#4##7???<769#1##7???<76:#1##7???<76;#1##7???<76<#1##7???<76=#1##7???<76>#1##7???<76?#1##7???<770#1##7???<771#1##7???<772#1##7???<773#1##7???<774#1##7???<775#1##7???<776#1##7???<777#1##7???<784#1##7???<785#1##7???<786#1##7???<787#1##7???<788#1##7???<789#1##7???<78:#1##7???<78;#1##7???<78<#1##7???<78<#4##7???<78=#1##7???<78>#1##7???<78?#1##7???<790#4##7???<794#4##7???<798#4##7???<79<#4##7???<7:0#4##7???<7:4#4##7???<7:8#8##7???<7;0#8##7???<7;8#8##7???<7<0#8##7???<7<8#8##7???<7=0#8##7???<7=8#8##7???<7>0#8##7???<7>8#8##7???<7?0#8##7???<7?8#8##7???<800#8##7???<808#8##7???<810#8##7???<818#8##7???<820#8##7???<828#8##7???<830#8##7???<838#8##7???<840#8##7???<848#8##7???<850#8##7???<858#8##7???<860#8##7???<868#8##7???<870#8##7???<878#8##7???<880#8##7???<888#8##7???<890#8##7???<898#8##7???<8:0#8##7???<8:8#8##7???<8;0#8##7???<8;8#8##7???<8<0#8##7???<8<8#8##7???<8=0#8##7???<8=8#8##7???<8>0#8##7???<8>8#8##7???<8?0#8##7???<8?8#8##7???<900#8##7???<908#8##7???<910#8##7???<918#8##7???<920#8##7???<928#8##7???<930#8##7???<938#8##7???<940#8##7???<948#8##7???<950#8##7???<958#8##7???<960#8##7???<968#8##7???<970#8##7???<978#8##7???<980#8##7???<988#8##7???<990#8##7???<998#8##7???<9:0#8##7???<9:8#8##7???<9;0#8##7???<9;8#8##7???<9<0#8##7???<9<8#8##7???<9=0#8##7???<9=8#8##7???<9>0#8##7???<9>8#8##7???<9?0#8##7???<9?8#8##7???<:00#8##7???<:08#8##7???<:10#8##7???<:18#8##7???<:20#8##7???<:28#8##7???<:30#8##7???<:38#8##7???<:40#8##7???<:48#8##7???<:50#8##7???<:58#8##7???<:60#8##7???<:68#8##7???<:70#8##7???<:78#8##7???<:80#8##7???<:88#8##7???<:90#8##7???<:98#8##7???<::0#8##7???<::8#8##7???<:;0#8##7???<:;8#8##7???<:<0#8##7???<:<8#4##7???<:<<#4##7???<:=0#4##7???<:=4#4##7???<:=8#4##7???<:=<#4##7???<:>0#1##7???<:>0#4##7???<:>1#1##7???<:>2#1##7???<:>3#1##7???<:>4#1##7???<:>4#4##7???<:>5#1##7???<:>6#1##7???<:>7#1##7???<:>8#4##7???<:><#4##7???<:?0#4##7???<:?4#4##7???<:?8#4##7???<:?<#4##7???<;00#8##7???<;08#8##7???<;10#8##7???<;18#8##7???<;20#8##7???<;28#8##7???<;30#8##7???<;38#8##7???<;40#8##7???<;48#8##7???<;50#8##7???<;58#8##7???<;60#8##7???<;68#8##7???<;70#8##7???<;78#8##7???<;80#8##7???<;88#8##7???<;90#8##7???<;98#8##7???<;:0#8##7???<;:8#8##7???<;;0#8##7???<;;8#8##7???<;<0#8##7???<;<8#8##7???<;=0#8##7???<;=8#8##7???<;>0#8##7???<;>8#8##7???<;?0#8##7???<;?8#8##7???<<00#8##7???<<08#8##7???<<10#8##7???<<18#8##7???<<20#8##7???<<28#8##7???<<30#8##7???<<38#8##7???<<40#8##7???<<48#8##7???<<50#8##7???<<58#8##7???<<60#8##7???<<68#8##7???<<70#8##7???<<74#4##7???<<78#4##7???<<78#8##7???<<7<#4##7???<<80#4##7???<<84#4##7???<<88#4##7???<<8<#1##7???<<8<#4##7???<<8=#1##7???<<8>#1##7???<<8?#1##7???<<90#1##7???<<91#1##7???<<92#1##7???<<93#1##7???<<94#1##7???<<94#4##7???<<95#1##7???<<96#1##7???<<97#1##7???<<98#4##7???<<9<#4##7???<<:0#1##7???<<:0#4##7???<<:1#1##7???<<:2#1##7???<<:3#1##7???<<:4#1##7???<<:5#1##7???<<:6#1##7???<<:7#1##7???<<:8#1##7???<<:9#1##7???<<::#1##7???<<:;#1##7???<<:<#1##7???<<:=#1##7???<<:>#1##7???<<:?#1##7???<<;0#1##7???<<;1#1##7???<<;2#1##7???<<;3#1##7???<<;4#1##7???<<;5#1##7???<<;6#1##7???<<;7#1##7???<<<<#1##7???<<<=#1##7???<<<>#1##7???<<<?#1##7???<<?<#1##7???<<?=#1##7???<<?>#1##7???<<??#1##7???<=00#1##7???<=01#1##7???<=02#1##7???<=03#1##7???<=04#1##7???<=05#1##7???<=06#1##7???<=07#1##7???<=08#1##7???<=09#1##7???<=0:#1##7???<=0;#1##7???<=0<#1##7???<=0=#1##7???<=0>#1##7???<=0?#1##7???<=10#1##7???<=10#4##7???<=11#1##7???<=12#1##7???<=13#1##7???<=14#4##7???<=18#1##7???<=18#4##7???<=19#1##7???<=1:#1##7???<=1;#1##7???<=1<#1##7???<=1<#4##7???<=1=#1##7???<=1>#1##7???<=1?#1##7???<=20#4##7???<=24#1##7???<=24#4##7???<=25#1##7???<=26#1##7???<=27#1##7???<=28#1##7???<=28#4##7???<=29#1##7???<=2:#1##7???<=2;#1##7???<=2<#4##7???<=30#1##7???<=30#4##7???<=31#1##7???<=32#1##7???<=33#1##7???<=34#1##7???<=34#4##7???<=35#1##7???<=36#1##7???<=37#1##7???<=38#4##7???<=3<#1##7???<=3<#4##7???<=3=#1##7???<=3>#1##7???<=3?#1##7???<=40#1##7???<=40#4##7???<=41#1##7???<=42#1##7???<=43#1##7???<=44#4##7???<=48#1##7???<=48#4##7???<=49#1##7???<=4:#1##7???<=4;#1##7???<=4<#1##7???<=4<#4##7???<=4=#1##7???<=4>#1##7???<=4?#1##7???<=50#4##7???<=54#1##7???<=54#4##7???<=55#1##7???<=56#1##7???<=57#1##7???<=58#1##7???<=58#4##7???<=59#1##7???<=5:#1##7???<=5;#1##7???<=5<#4##7???<=60#4##7???<=64#1##7???<=64#4##7???<=65#1##7???<=66#1##7???<=67#1##7???<=68#1##7???<=69#1##7???<=6:#1##7???<=6;#1##7???<=6<#1##7???<=6=#1##7???<=6>#1##7???<=6?#1##7???<=70#1##7???<=71#1##7???<=72#1##7???<=73#1##7???<=74#1##7???<=75#1##7???<=76#1##7???<=77#1##7???<=78#1##7???<=78#4##7???<=79#1##7???<=7:#1##7???<=7;#1##7???<=7<#4##7???<=80#1##7???<=80#4##7???<=81#1##7???<=82#1##7???<=83#1##7???<=84#1##7???<=84#4##7???<=85#1##7???<=86#1##7???<=87#1##7???<=88#4##7???<=8<#1##7???<=8<#4##7???<=8=#1##7???<=8>#1##7???<=8?#1##7???<=90#1##7???<=90#4##7???<=91#1##7???<=92#1##7???<=93#1##7???<=94#4##7???<=98#1##7???<=98#4##7???<=99#1##7???<=9:#1##7???<=9;#1##7???<=9<#1##7???<=9<#4##7???<=9=#1##7???<=9>#1##7???<=9?#1##7???<=:0#4##7???<=:4#1##7???<=:4#4##7???<=:5#1##7???<=:6#1##7???<=:7#1##7???<=:8#1##7???<=:8#4##7???<=:9#1##7???<=::#1##7???<=:;#1##7???<=:<#4##7???<=;0#1##7???<=;0#4##7???<=;1#1##7???<=;2#1##7???<=;3#1##7???<=;4#1##7???<=;4#4##7???<=;5#1##7???<=;6#1##7???<=;7#1##7???<=;8#4##7???<=;<#1##7???<=;<#4##7???<=;=#1##7???<=;>#1##7???<=;?#1##7???<=<0#1##7???<=<1#1##7???<=<2#1##7???<=<3#1##7???<=>8#1##7???<=>9#1##7???<=>:#1##7???<=>;#1##7???<=><#1##7???<=>=#1##7???<=>>#1##7???<=>?#1##7???<=?0#1##7???<=?1#1##7???<=?2#1##7???<=?3#1##7???<=?4#1##7???<=?5#1##7???<=?6#1##7???<=?7#1##7???<>04#1##7???<>04#4##7???<>05#1##7???<>06#1##7???<>07#1##7???<>08#4##7???<>0<#1##7???<>0<#4##7???<>0=#1##7???<>0>#1##7???<>0?#1##7???<>10#1##7???<>10#4##7???<>11#1##7???<>12#1##7???<>13#1##7???<>14#4##7???<>18#4##7???<>1<#4##7???<>20#4##7???<>24#4##7???<>28#4##7???<>28#8##7???<>30#8##7???<>38#4##7???<>38#8##7???<>3<#4##7???<>40#4##7???<>40#8##7???<>44#4##7???<>48#4##7???<>4<#4##7???<>50#1##7???<>50#4##7???<>51#1##7???<>52#1##7???<>53#1##800222:4#1##800222:4#4##800222:5#1##800222:6#1##800222:7#1##800222:8#4##800222:<#4##800222;0#1##800222;0#4##800222;1#1##800222;2#1##800222;3#1##80023714#1##80023714#4##80023715#1##80023716#1##80023717#1##80023718#4##8002371<#4##80023720#4##80023724#4##80023728#4##8002372<#4##80023730#8##80023738#8##80023740#8##80023748#8##80023750#8##80023758#8##80023760#8##80023768#8##80023770#8##80023778#8##80023780#8##80023788#8##80023790#8##80023798#8##800237:0#8##800237:8#8##800237;0#8##800237;8#8##800237<0#8##800237<8#8##800237=0#8##800237=8#8##800237>0#8##800237>8#8##800237?0#8##800237?8#8##80023800#8##80023808#8##80023810#8##80023818#8##80023820#8##80023828#8##80023830#8##80023838#8##80023840#8##80023848#8##80023850#8##80023858#8##80023858#4##8002385<#4##80023860#8##80023860#4##80023864#4##80023868#8##80023868#4##8002386<#4##80023870#1##80023870#4##80023871#1##80023872#1##80023873#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",259$2-140#140##15<3<0#8##15<410#1##15=330#8##6;3;50#1##6;3;58#4##6;3;60#8##6;3=70#4##7???<748#1##7???<749#1##7???<74:#1##7???<74;#1##7???<74<#1##7???<74<#4##7???<74=#1##7???<74>#1##7???<74?#1##7???<750#4##7???<754#1##7???<754#4##7???<755#1##7???<756#1##7???<757#1##7???<75<#1##7???<75=#1##7???<75>#1##7???<75?#1##7???<760#1##7???<760#4##7???<761#1##7???<762#1##7???<763#1##7???<764#4##7???<768#1##7???<768#4##7???<769#1##7???<76:#1##7???<76;#1##7???<76<#1##7???<76=#1##7???<76>#1##7???<76?#1##7???<770#1##7???<771#1##7???<772#1##7???<773#1##7???<774#1##7???<775#1##7???<776#1##7???<777#1##7???<784#1##7???<785#1##7???<786#1##7???<787#1##7???<788#1##7???<789#1##7???<78:#1##7???<78;#1##7???<78<#1##7???<78<#4##7???<78=#1##7???<78>#1##7???<78?#1##7???<790#4##7???<794#4##7???<798#4##7???<79<#4##7???<7:0#4##7???<7:4#4##7???<7:8#8##7???<7;0#8##7???<7;8#8##7???<7<0#8##7???<7<8#8##7???<7=0#8##7???<7=8#8##7???<7>0#8##7???<7>8#8##7???<7?0#8##7???<7?8#8##7???<800#8##7???<808#8##7???<810#8##7???<818#8##7???<820#8##7???<828#8##7???<830#8##7???<838#8##7???<840#8##7???<848#8##7???<850#8##7???<858#8##7???<860#8##7???<868#8##7???<870#8##7???<878#8##7???<880#8##7???<888#8##7???<890#8##7???<898#8##7???<8:0#8##7???<8:8#8##7???<8;0#8##7???<8;8#8##7???<8<0#8##7???<8<8#8##7???<8=0#8##7???<8=8#8##7???<8>0#8##7???<8>8#8##7???<8?0#8##7???<8?8#8##7???<900#8##7???<908#8##7???<910#8##7???<918#8##7???<920#8##7???<928#8##7???<930#8##7???<938#8##7???<940#8##7???<948#8##7???<950#8##7???<958#8##7???<960#8##7???<968#8##7???<970#8##7???<978#8##7???<980#8##7???<988#8##7???<990#8##7???<998#8##7???<9:0#8##7???<9:8#8##7???<9;0#8##7???<9;8#8##7???<9<0#8##7???<9<8#8##7???<9=0#8##7???<9=8#8##7???<9>0#8##7???<9>8#8##7???<9?0#8##7???<9?8#8##7???<:00#8##7???<:08#8##7???<:10#8##7???<:18#8##7???<:20#8##7???<:28#8##7???<:30#8##7???<:38#8##7???<:40#8##7???<:48#8##7???<:50#8##7???<:58#8##7???<:60#8##7???<:68#8##7???<:70#8##7???<:78#8##7???<:80#8##7???<:88#8##7???<:90#8##7???<:98#8##7???<::0#8##7???<::8#8##7???<:;0#8##7???<:;8#8##7???<:<0#8##7???<:<8#4##7???<:<<#4##7???<:=0#4##7???<:=4#4##7???<:=8#4##7???<:=<#4##7???<:>0#1##7???<:>0#4##7???<:>1#1##7???<:>2#1##7???<:>3#1##7???<:>4#1##7???<:>4#4##7???<:>5#1##7???<:>6#1##7???<:>7#1##7???<:>8#4##7???<:><#4##7???<:?0#4##7???<:?4#4##7???<:?8#4##7???<:?<#4##7???<;00#8##7???<;08#8##7???<;10#8##7???<;18#8##7???<;20#8##7???<;28#8##7???<;30#8##7???<;38#8##7???<;40#8##7???<;48#8##7???<;50#8##7???<;58#8##7???<;60#8##7???<;68#8##7???<;70#8##7???<;78#8##7???<;80#8##7???<;88#8##7???<;90#8##7???<;98#8##7???<;:0#8##7???<;:8#8##7???<;;0#8##7???<;;8#8##7???<;<0#8##7???<;<8#8##7???<;=0#8##7???<;=8#8##7???<;>0#8##7???<;>8#8##7???<;?0#8##7???<;?8#8##7???<<00#8##7???<<08#8##7???<<10#8##7???<<18#8##7???<<20#8##7???<<28#8##7???<<30#8##7???<<38#8##7???<<40#8##7???<<48#8##7???<<50#8##7???<<58#8##7???<<60#8##7???<<68#8##7???<<70#8##7???<<74#4##7???<<78#4##7???<<78#8##7???<<7<#4##7???<<80#4##7???<<84#4##7???<<88#4##7???<<8<#1##7???<<8<#4##7???<<8=#1##7???<<8>#1##7???<<8?#1##7???<<90#1##7???<<91#1##7???<<92#1##7???<<93#1##7???<<94#1##7???<<94#4##7???<<95#1##7???<<96#1##7???<<97#1##7???<<98#4##7???<<9<#4##7???<<:0#1##7???<<:0#4##7???<<:1#1##7???<<:2#1##7???<<:3#1##7???<<:4#1##7???<<:5#1##7???<<:6#1##7???<<:7#1##7???<<:8#1##7???<<:9#1##7???<<::#1##7???<<:;#1##7???<<:<#1##7???<<:=#1##7???<<:>#1##7???<<:?#1##7???<<;0#1##7???<<;1#1##7???<<;2#1##7???<<;3#1##7???<<;4#1##7???<<;5#1##7???<<;6#1##7???<<;7#1##7???<<<<#1##7???<<<=#1##7???<<<>#1##7???<<<?#1##7???<<?<#1##7???<<?=#1##7???<<?>#1##7???<<??#1##7???<=00#1##7???<=01#1##7???<=02#1##7???<=03#1##7???<=04#1##7???<=05#1##7???<=06#1##7???<=07#1##7???<=08#1##7???<=09#1##7???<=0:#1##7???<=0;#1##7???<=0<#1##7???<=0=#1##7???<=0>#1##7???<=0?#1##7???<=10#1##7???<=10#4##7???<=11#1##7???<=12#1##7???<=13#1##7???<=14#4##7???<=18#1##7???<=18#4##7???<=19#1##7???<=1:#1##7???<=1;#1##7???<=1<#1##7???<=1<#4##7???<=1=#1##7???<=1>#1##7???<=1?#1##7???<=20#4##7???<=24#1##7???<=24#4##7???<=25#1##7???<=26#1##7???<=27#1##7???<=28#1##7???<=28#4##7???<=29#1##7???<=2:#1##7???<=2;#1##7???<=2<#4##7???<=30#1##7???<=30#4##7???<=31#1##7???<=32#1##7???<=33#1##7???<=34#1##7???<=34#4##7???<=35#1##7???<=36#1##7???<=37#1##7???<=38#4##7???<=3<#1##7???<=3<#4##7???<=3=#1##7???<=3>#1##7???<=3?#1##7???<=40#1##7???<=40#4##7???<=41#1##7???<=42#1##7???<=43#1##7???<=44#4##7???<=48#1##7???<=48#4##7???<=49#1##7???<=4:#1##7???<=4;#1##7???<=4<#1##7???<=4<#4##7???<=4=#1##7???<=4>#1##7???<=4?#1##7???<=50#4##7???<=54#1##7???<=54#4##7???<=55#1##7???<=56#1##7???<=57#1##7???<=58#1##7???<=58#4##7???<=59#1##7???<=5:#1##7???<=5;#1##7???<=5<#4##7???<=60#4##7???<=64#1##7???<=64#4##7???<=65#1##7???<=66#1##7???<=67#1##7???<=68#1##7???<=69#1##7???<=6:#1##7???<=6;#1##7???<=6<#1##7???<=6=#1##7???<=6>#1##7???<=6?#1##7???<=70#1##7???<=71#1##7???<=72#1##7???<=73#1##7???<=74#1##7???<=75#1##7???<=76#1##7???<=77#1##7???<=78#1##7???<=78#4##7???<=79#1##7???<=7:#1##7???<=7;#1##7???<=7<#4##7???<=80#1##7???<=80#4##7???<=81#1##7???<=82#1##7???<=83#1##7???<=84#1##7???<=84#4##7???<=85#1##7???<=86#1##7???<=87#1##7???<=88#4##7???<=8<#1##7???<=8<#4##7???<=8=#1##7???<=8>#1##7???<=8?#1##7???<=90#1##7???<=90#4##7???<=91#1##7???<=92#1##7???<=93#1##7???<=94#4##7???<=98#1##7???<=98#4##7???<=99#1##7???<=9:#1##7???<=9;#1##7???<=9<#1##7???<=9<#4##7???<=9=#1##7???<=9>#1##7???<=9?#1##7???<=:0#4##7???<=:4#1##7???<=:4#4##7???<=:5#1##7???<=:6#1##7???<=:7#1##7???<=:8#1##7???<=:8#4##7???<=:9#1##7???<=::#1##7???<=:;#1##7???<=:<#4##7???<=;0#1##7???<=;0#4##7???<=;1#1##7???<=;2#1##7???<=;3#1##7???<=;4#1##7???<=;4#4##7???<=;5#1##7???<=;6#1##7???<=;7#1##7???<=;8#4##7???<=;<#1##7???<=;<#4##7???<=;=#1##7???<=;>#1##7???<=;?#1##7???<=<0#1##7???<=<1#1##7???<=<2#1##7???<=<3#1##7???<=>8#1##7???<=>9#1##7???<=>:#1##7???<=>;#1##7???<=><#1##7???<=>=#1##7???<=>>#1##7???<=>?#1##7???<=?0#1##7???<=?1#1##7???<=?2#1##7???<=?3#1##7???<=?4#1##7???<=?5#1##7???<=?6#1##7???<=?7#1##7???<>04#1##7???<>04#4##7???<>05#1##7???<>06#1##7???<>07#1##7???<>08#4##7???<>0<#1##7???<>0<#4##7???<>0=#1##7???<>0>#1##7???<>0?#1##7???<>10#1##7???<>10#4##7???<>11#1##7???<>12#1##7???<>13#1##7???<>14#4##7???<>18#4##7???<>1<#4##7???<>20#4##7???<>24#4##7???<>28#4##7???<>28#8##7???<>30#8##7???<>38#4##7???<>38#8##7???<>3<#4##7???<>40#4##7???<>40#8##7???<>44#4##7???<>48#4##7???<>4<#4##7???<>50#1##7???<>50#4##7???<>51#1##7???<>52#1##7???<>53#1##800222:4#1##800222:4#4##800222:5#1##800222:6#1##800222:7#1##800222:8#4##800222:<#4##800222;0#1##800222;0#4##800222;1#1##800222;2#1##800222;3#1##80023714#1##80023714#4##80023715#1##80023716#1##80023717#1##80023718#4##8002371<#4##80023720#4##80023724#4##80023728#4##8002372<#4##80023730#8##80023738#8##80023740#8##80023748#8##80023750#8##80023758#8##80023760#8##80023768#8##80023770#8##80023778#8##80023780#8##80023788#8##80023790#8##80023798#8##800237:0#8##800237:8#8##800237;0#8##800237;8#8##800237<0#8##800237<8#8##800237=0#8##800237=8#8##800237>0#8##800237>8#8##800237?0#8##800237?8#8##80023800#8##80023808#8##80023810#8##80023818#8##80023820#8##80023828#8##80023830#8##80023838#8##80023840#8##80023848#8##80023850#8##80023858#8##80023858#4##8002385<#4##80023860#8##80023860#4##80023864#4##80023868#8##80023868#4##8002386<#4##80023870#1##80023870#4##80023871#1##80023872#1##80023873#1"%pstring).
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#1379=8#1379=8#5=#1379=8,20##137=3<+$2-10$3#693;00#^#1##$:$9$:$:^#6##^#>#???????????????#?????0000000000^#?#?????0000000000#5>$12$13$14$15$16$17$18$19$1:$1;#15=2?0$1=$1>$1?,,4?0!$2-30,8$:!$2-28,8#13?<14!$2-20,8$:!$2-18,8#137=34!##15<3<0,8#!##15=330,8#!##80023868,8#!##80023860,8#!##80023858,8#!##80023850,8#!##80023848,8#!##80023840,8#!##80023838,8#!##80023830,8#!##80023828,8#!##80023820,8#!##80023818,8#!##80023810,8#!##80023808,8#!##80023800,8#!##800237?8,8#!##800237?0,8#!##800237>8,8#!##800237>0,8#!##800237=8,8#!##800237=0,8#!##800237<8,8#!##800237<0,8#!##800237;8,8#!##800237;0,8#!##800237:8,8#!##800237:0,8#!##80023798,8#!##80023790,8#!##80023788,8#!##80023780,8#!##80023778,8#!##80023770,8#!##80023768,8#!##80023760,8#!##80023758,8#!##80023750,8#!##80023748,8#!##80023740,8#!##80023738,8#!##80023730,8#!##8002372<,4#!##80023728,4#!##80023724,4#!##80023720,4#!##8002371<,4#!##80023718,4#!##80023870,4#!##80023714,4#!$2-138,8^#2#!$2-130,8#15<3:0!$2-128,8#1=010!$2-120,8#2!$2-118,8#1!$2-110,8^#2#!$2-108,8#67?>0!##800222:<,4#!##800222:8,4#!##800222;0,4#!##800222:4,4#!##7???<>40,8#!##7???<>38,8#!##7???<>30,8#!##7???<>28,8#!##7???<>24,4#!##7???<>20,4#!##7???<>1<,4#!##7???<>4<,4#!##7???<>48,4#!##7???<>18,4#!##7???<>14,4#!##7???<>50,4#!##7???<>10,4#!##7???<>08,4#!##7???<>04,4#!##7???<>0<,4#!##7???<=?6,1#!##7???<=?5,1#!##7???<=?7,1#!##7???<=?4,1#!##7???<=?2,1#!##7???<=?1,1#!##7???<=?3,1#!##7???<=?0,1#!##7???<=>>,1#!##7???<=>=,1#!##7???<=>?,1#!##7???<=><,1#!##7???<=>:,1#!##7???<=>9,1#!##7???<=>;,1#!##7???<=>8,1#!##7???<=<2,1#!##7???<=<1,1#!##7???<=<3,1#!##7???<=<0,1#!##7???<=;8,4#!##7???<=;4,4#!##7???<=;<,4#!##7???<=:<,4#!##7???<=:8,4#!##7???<=;0,4#!##7???<=:0,4#!##7???<=9<,4#!##7???<=:4,4#!##7???<=94,4#!##7???<=90,4#!##7???<=98,4#!##7???<=88,4#!##7???<=84,4#!##7???<=8<,4#!##7???<=7<,4#!##7???<=78,4#!##7???<=80,4#!##7???<=74,1#!##7???<=73,1#!##7???<=76,1#!##7???<=75,1#!##7???<=72,1#!##7???<=71,1#!##7???<=77,1#!##7???<=70,1#!##7???<=6<,1#!##7???<=6;,1#!##7???<=6>,1#!##7???<=6=,1#!##7???<=6:,1#!##7???<=69,1#!##7???<=6?,1#!##7???<=68,1#!##7???<=60,4#!##7???<=5<,4#!##7???<=64,4#!##7???<=58,4#!##7???<=50,4#!##7???<=4<,4#!##7???<=54,4#!##7???<=44,4#!##7???<=40,4#!##7???<=48,4#!##7???<=38,4#!##7???<=34,4#!##7???<=3<,4#!##7???<=2<,4#!##7???<=28,4#!##7???<=30,4#!##7???<=20,4#!##7???<=1<,4#!##7???<=24,4#!##7???<=14,4#!##7???<=10,4#!##7???<=18,4#!##7???<=0>,1#!##7???<=0=,1#!##7???<=0?,1#!##7???<=0<,1#!##7???<=08,1#!##7???<=07,1#!##7???<=0:,1#!##7???<=09,1#!##7???<=06,1#!##7???<=05,1#!##7???<=0;,1#!##7???<=04,1#!##7???<=00,1#!##7???<<??,1#!##7???<=02,1#!##7???<=01,1#!##7???<<?>,1#!##7???<<?=,1#!##7???<=03,1#!##7???<<?<,1#!##7???<<<>,1#!##7???<<<=,1#!##7???<<<?,1#!##7???<<<<,1#!##7???<<;6,1#!##7???<<;5,1#!##7???<<;7,1#!##7???<<;4,1#!##7???<<;2,1#!##7???<<;1,1#!##7???<<;3,1#!##7???<<;0,1#!##7???<<:>,1#!##7???<<:=,1#!##7???<<:?,1#!##7???<<:<,1#!##7???<<::,1#!##7???<<:9,1#!##7???<<:;,1#!##7???<<:8,1#!##7???<<:6,1#!##7???<<:5,1#!##7???<<:7,1#!##7???<<:4,1#!##7???<<9<,4#!##7???<<98,4#!##7???<<:0,4#!##7???<<94,4#!##7???<<92,1#!##7???<<91,1#!##7???<<93,1#!##7???<<90,1#!##7???<<78,8#!##7???<<70,8#!##7???<<68,8#!##7???<<60,8#!##7???<<58,8#!##7???<<50,8#!##7???<<48,8#!##7???<<40,8#!##7???<<38,8#!##7???<<30,8#!##7???<<28,8#!##7???<<20,8#!##7???<<18,8#!##7???<<10,8#!##7???<<08,8#!##7???<<00,8#!##7???<;?8,8#!##7???<;?0,8#!##7???<;>8,8#!##7???<;>0,8#!##7???<;=8,8#!##7???<;=0,8#!##7???<;<8,8#!##7???<;<0,8#!##7???<;;8,8#!##7???<;;0,8#!##7???<;:8,8#!##7???<;:0,8#!##7???<;98,8#!##7???<;90,8#!##7???<;88,8#!##7???<;80,8#!##7???<;78,8#!##7???<;70,8#!##7???<;68,8#!##7???<;60,8#!##7???<;58,8#!##7???<;50,8#!##7???<;48,8#!##7???<;40,8#!##7???<;38,8#!##7???<;30,8#!##7???<;28,8#!##7???<;20,8#!##7???<;18,8#!##7???<;10,8#!##7???<;08,8#!##7???<;00,8#!##7???<<80,4#!##7???<:?<,4#!##7???<:?8,4#!##7???<:?4,4#!##7???<:?0,4#!##7???<<88,4#!##7???<<84,4#!##7???<:><,4#!##7???<:>8,4#!##7???<<8<,4#!##7???<:>4,4#!##7???<:<0,8#!##7???<:;8,8#!##7???<:;0,8#!##7???<::8,8#!##7???<::0,8#!##7???<:98,8#!##7???<:90,8#!##7???<:88,8#!##7???<:80,8#!##7???<:78,8#!##7???<:70,8#!##7???<:68,8#!##7???<:60,8#!##7???<:58,8#!##7???<:50,8#!##7???<:48,8#!##7???<:40,8#!##7???<:38,8#!##7???<:30,8#!##7???<:28,8#!##7???<:20,8#!##7???<:18,8#!##7???<:10,8#!##7???<:08,8#!##7???<:00,8#!##7???<9?8,8#!##7???<9?0,8#!##7???<9>8,8#!##7???<9>0,8#!##7???<9=8,8#!##7???<9=0,8#!##7???<9<8,8#!##7???<9<0,8#!##7???<9;8,8#!##7???<9;0,8#!##7???<9:8,8#!##7???<9:0,8#!##7???<998,8#!##7???<990,8#!##7???<988,8#!##7???<980,8#!##7???<978,8#!##7???<970,8#!##7???<968,8#!##7???<960,8#!##7???<958,8#!##7???<950,8#!##7???<948,8#!##7???<940,8#!##7???<938,8#!##7???<930,8#!##7???<928,8#!##7???<920,8#!##7???<918,8#!##7???<910,8#!##7???<908,8#!##7???<900,8#!##7???<8?8,8#!##7???<8?0,8#!##7???<8>8,8#!##7???<8>0,8#!##7???<8=8,8#!##7???<8=0,8#!##7???<8<8,8#!##7???<8<0,8#!##7???<8;8,8#!##7???<8;0,8#!##7???<8:8,8#!##7???<8:0,8#!##7???<898,8#!##7???<890,8#!##7???<888,8#!##7???<880,8#!##7???<878,8#!##7???<870,8#!##7???<868,8#!##7???<860,8#!##7???<858,8#!##7???<850,8#!##7???<848,8#!##7???<840,8#!##7???<838,8#!##7???<830,8#!##7???<828,8#!##7???<820,8#!##7???<818,8#!##7???<810,8#!##7???<808,8#!##7???<800,8#!##7???<7?8,8#!##7???<7?0,8#!##7???<7>8,8#!##7???<7>0,8#!##7???<7=8,8#!##7???<7=0,8#!##7???<7<8,8#!##7???<7<0,8#!##7???<7;8,8#!##7???<7;0,8#!##7???<7:8,8#!##7???<:=4,4#!##7???<:=0,4#!##7???<:<<,4#!##7???<:<8,4#!##7???<7:4,4#!##7???<7:0,4#!##7???<79<,4#!##7???<798,4#!##7???<:=<,4#!##7???<:=8,4#!##7???<794,4#!##7???<790,4#!##7???<:>0,4#!##7???<78<,4#!##7???<78:,1#!##7???<789,1#!##7???<78;,1#!##7???<788,1#!##7???<786,1#!##7???<785,1#!##7???<787,1#!##7???<784,1#!##7???<774,1#!##7???<773,1#!##7???<776,1#!##7???<775,1#!##7???<772,1#!##7???<771,1#!##7???<777,1#!##7???<770,1#!##7???<76>,1#!##7???<76=,1#!##7???<76?,1#!##7???<76<,1#!##7???<764,4#!##7???<760,4#!##7???<768,4#!##7???<75>,1#!##7???<75=,1#!##7???<75?,1#!##7???<75<,1#!##7???<750,4#!##7???<74<,4#!##7???<754,4#!##7???<74:,1#!##7???<749,1#!##7???<74;,1#!##7???<748,1#!$2-=0,8#1>?520!$2-=8,8#160760!$2-<8,8#160770!$2-<0,8#160768!$2->8,8#2<!$2-?0,8#15=2?0!$2-?8,8#15=338!$2->0,8#15;8:0!$2-;8,8$1;!$2-;0,8$1:!$2-:8,8$19!$2-:0,8$18!$2-98,8$17!$2-90,8$16!$2-88,8$15!$2-80,8$14!$2-78,8$13!$2-70,8$12!$2-68,8#1508?0!$2-60,8#15<3<0!$2-58,8#68274!$2-50,8#1508?0!$2-48,8#=5694!$2-38,8#137<:<!##15<410,1#1!$2-40,8#1508?0!##6;3;50,1#1!##6;3;60,8#!##6;3;58,4#20!##6;3=70,4$2<!$2-10,8$8!$2-8,8$1'$2#7???7?811000#800000000000&$2#10($2-140#140,$2-140#8,$2-100#8%#10000#158000(##15<3<0#8(##15<410#1(##15=330#8(##6;3;50#1(##6;3;58#4(##6;3;60#8(##6;3=70#4(##7???<748#1(##7???<749#1(##7???<74:#1(##7???<74;#1(##7???<74<#1(##7???<74<#4(##7???<74=#1(##7???<74>#1(##7???<74?#1(##7???<750#4(##7???<754#1(##7???<754#4(##7???<755#1(##7???<756#1(##7???<757#1(##7???<75<#1(##7???<75=#1(##7???<75>#1(##7???<75?#1(##7???<760#1(##7???<760#4(##7???<761#1(##7???<762#1(##7???<763#1(##7???<764#4(##7???<768#1(##7???<768#4(##7???<769#1(##7???<76:#1(##7???<76;#1(##7???<76<#1(##7???<76=#1(##7???<76>#1(##7???<76?#1(##7???<770#1(##7???<771#1(##7???<772#1(##7???<773#1(##7???<774#1(##7???<775#1(##7???<776#1(##7???<777#1(##7???<784#1(##7???<785#1(##7???<786#1(##7???<787#1(##7???<788#1(##7???<789#1(##7???<78:#1(##7???<78;#1(##7???<78<#1(##7???<78<#4(##7???<78=#1(##7???<78>#1(##7???<78?#1(##7???<790#4(##7???<794#4(##7???<798#4(##7???<79<#4(##7???<7:0#4(##7???<7:4#4(##7???<7:8#8(##7???<7;0#8(##7???<7;8#8(##7???<7<0#8(##7???<7<8#8(##7???<7=0#8(##7???<7=8#8(##7???<7>0#8(##7???<7>8#8(##7???<7?0#8(##7???<7?8#8(##7???<800#8(##7???<808#8(##7???<810#8(##7???<818#8(##7???<820#8(##7???<828#8(##7???<830#8(##7???<838#8(##7???<840#8(##7???<848#8(##7???<850#8(##7???<858#8(##7???<860#8(##7???<868#8(##7???<870#8(##7???<878#8(##7???<880#8(##7???<888#8(##7???<890#8(##7???<898#8(##7???<8:0#8(##7???<8:8#8(##7???<8;0#8(##7???<8;8#8(##7???<8<0#8(##7???<8<8#8(##7???<8=0#8(##7???<8=8#8(##7???<8>0#8(##7???<8>8#8(##7???<8?0#8(##7???<8?8#8(##7???<900#8(##7???<908#8(##7???<910#8(##7???<918#8(##7???<920#8(##7???<928#8(##7???<930#8(##7???<938#8(##7???<940#8(##7???<948#8(##7???<950#8(##7???<958#8(##7???<960#8(##7???<968#8(##7???<970#8(##7???<978#8(##7???<980#8(##7???<988#8(##7???<990#8(##7???<998#8(##7???<9:0#8(##7???<9:8#8(##7???<9;0#8(##7???<9;8#8(##7???<9<0#8(##7???<9<8#8(##7???<9=0#8(##7???<9=8#8(##7???<9>0#8(##7???<9>8#8(##7???<9?0#8(##7???<9?8#8(##7???<:00#8(##7???<:08#8(##7???<:10#8(##7???<:18#8(##7???<:20#8(##7???<:28#8(##7???<:30#8(##7???<:38#8(##7???<:40#8(##7???<:48#8(##7???<:50#8(##7???<:58#8(##7???<:60#8(##7???<:68#8(##7???<:70#8(##7???<:78#8(##7???<:80#8(##7???<:88#8(##7???<:90#8(##7???<:98#8(##7???<::0#8(##7???<::8#8(##7???<:;0#8(##7???<:;8#8(##7???<:<0#8(##7???<:<8#4(##7???<:<<#4(##7???<:=0#4(##7???<:=4#4(##7???<:=8#4(##7???<:=<#4(##7???<:>0#1(##7???<:>0#4(##7???<:>1#1(##7???<:>2#1(##7???<:>3#1(##7???<:>4#1(##7???<:>4#4(##7???<:>5#1(##7???<:>6#1(##7???<:>7#1(##7???<:>8#4(##7???<:><#4(##7???<:?0#4(##7???<:?4#4(##7???<:?8#4(##7???<:?<#4(##7???<;00#8(##7???<;08#8(##7???<;10#8(##7???<;18#8(##7???<;20#8(##7???<;28#8(##7???<;30#8(##7???<;38#8(##7???<;40#8(##7???<;48#8(##7???<;50#8(##7???<;58#8(##7???<;60#8(##7???<;68#8(##7???<;70#8(##7???<;78#8(##7???<;80#8(##7???<;88#8(##7???<;90#8(##7???<;98#8(##7???<;:0#8(##7???<;:8#8(##7???<;;0#8(##7???<;;8#8(##7???<;<0#8(##7???<;<8#8(##7???<;=0#8(##7???<;=8#8(##7???<;>0#8(##7???<;>8#8(##7???<;?0#8(##7???<;?8#8(##7???<<00#8(##7???<<08#8(##7???<<10#8(##7???<<18#8(##7???<<20#8(##7???<<28#8(##7???<<30#8(##7???<<38#8(##7???<<40#8(##7???<<48#8(##7???<<50#8(##7???<<58#8(##7???<<60#8(##7???<<68#8(##7???<<70#8(##7???<<74#4(##7???<<78#4(##7???<<78#8(##7???<<7<#4(##7???<<80#4(##7???<<84#4(##7???<<88#4(##7???<<8<#1(##7???<<8<#4(##7???<<8=#1(##7???<<8>#1(##7???<<8?#1(##7???<<90#1(##7???<<91#1(##7???<<92#1(##7???<<93#1(##7???<<94#1(##7???<<94#4(##7???<<95#1(##7???<<96#1(##7???<<97#1(##7???<<98#4(##7???<<9<#4(##7???<<:0#1(##7???<<:0#4(##7???<<:1#1(##7???<<:2#1(##7???<<:3#1(##7???<<:4#1(##7???<<:5#1(##7???<<:6#1(##7???<<:7#1(##7???<<:8#1(##7???<<:9#1(##7???<<::#1(##7???<<:;#1(##7???<<:<#1(##7???<<:=#1(##7???<<:>#1(##7???<<:?#1(##7???<<;0#1(##7???<<;1#1(##7???<<;2#1(##7???<<;3#1(##7???<<;4#1(##7???<<;5#1(##7???<<;6#1(##7???<<;7#1(##7???<<<<#1(##7???<<<=#1(##7???<<<>#1(##7???<<<?#1(##7???<<?<#1(##7???<<?=#1(##7???<<?>#1(##7???<<??#1(##7???<=00#1(##7???<=01#1(##7???<=02#1(##7???<=03#1(##7???<=04#1(##7???<=05#1(##7???<=06#1(##7???<=07#1(##7???<=08#1(##7???<=09#1(##7???<=0:#1(##7???<=0;#1(##7???<=0<#1(##7???<=0=#1(##7???<=0>#1(##7???<=0?#1(##7???<=10#1(##7???<=10#4(##7???<=11#1(##7???<=12#1(##7???<=13#1(##7???<=14#4(##7???<=18#1(##7???<=18#4(##7???<=19#1(##7???<=1:#1(##7???<=1;#1(##7???<=1<#1(##7???<=1<#4(##7???<=1=#1(##7???<=1>#1(##7???<=1?#1(##7???<=20#4(##7???<=24#1(##7???<=24#4(##7???<=25#1(##7???<=26#1(##7???<=27#1(##7???<=28#1(##7???<=28#4(##7???<=29#1(##7???<=2:#1(##7???<=2;#1(##7???<=2<#4(##7???<=30#1(##7???<=30#4(##7???<=31#1(##7???<=32#1(##7???<=33#1(##7???<=34#1(##7???<=34#4(##7???<=35#1(##7???<=36#1(##7???<=37#1(##7???<=38#4(##7???<=3<#1(##7???<=3<#4(##7???<=3=#1(##7???<=3>#1(##7???<=3?#1(##7???<=40#1(##7???<=40#4(##7???<=41#1(##7???<=42#1(##7???<=43#1(##7???<=44#4(##7???<=48#1(##7???<=48#4(##7???<=49#1(##7???<=4:#1(##7???<=4;#1(##7???<=4<#1(##7???<=4<#4(##7???<=4=#1(##7???<=4>#1(##7???<=4?#1(##7???<=50#4(##7???<=54#1(##7???<=54#4(##7???<=55#1(##7???<=56#1(##7???<=57#1(##7???<=58#1(##7???<=58#4(##7???<=59#1(##7???<=5:#1(##7???<=5;#1(##7???<=5<#4(##7???<=60#4(##7???<=64#1(##7???<=64#4(##7???<=65#1(##7???<=66#1(##7???<=67#1(##7???<=68#1(##7???<=69#1(##7???<=6:#1(##7???<=6;#1(##7???<=6<#1(##7???<=6=#1(##7???<=6>#1(##7???<=6?#1(##7???<=70#1(##7???<=71#1(##7???<=72#1(##7???<=73#1(##7???<=74#1(##7???<=75#1(##7???<=76#1(##7???<=77#1(##7???<=78#1(##7???<=78#4(##7???<=79#1(##7???<=7:#1(##7???<=7;#1(##7???<=7<#4(##7???<=80#1(##7???<=80#4(##7???<=81#1(##7???<=82#1(##7???<=83#1(##7???<=84#1(##7???<=84#4(##7???<=85#1(##7???<=86#1(##7???<=87#1(##7???<=88#4(##7???<=8<#1(##7???<=8<#4(##7???<=8=#1(##7???<=8>#1(##7???<=8?#1(##7???<=90#1(##7???<=90#4(##7???<=91#1(##7???<=92#1(##7???<=93#1(##7???<=94#4(##7???<=98#1(##7???<=98#4(##7???<=99#1(##7???<=9:#1(##7???<=9;#1(##7???<=9<#1(##7???<=9<#4(##7???<=9=#1(##7???<=9>#1(##7???<=9?#1(##7???<=:0#4(##7???<=:4#1(##7???<=:4#4(##7???<=:5#1(##7???<=:6#1(##7???<=:7#1(##7???<=:8#1(##7???<=:8#4(##7???<=:9#1(##7???<=::#1(##7???<=:;#1(##7???<=:<#4(##7???<=;0#1(##7???<=;0#4(##7???<=;1#1(##7???<=;2#1(##7???<=;3#1(##7???<=;4#1(##7???<=;4#4(##7???<=;5#1(##7???<=;6#1(##7???<=;7#1(##7???<=;8#4(##7???<=;<#1(##7???<=;<#4(##7???<=;=#1(##7???<=;>#1(##7???<=;?#1(##7???<=<0#1(##7???<=<1#1(##7???<=<2#1(##7???<=<3#1(##7???<=>8#1(##7???<=>9#1(##7???<=>:#1(##7???<=>;#1(##7???<=><#1(##7???<=>=#1(##7???<=>>#1(##7???<=>?#1(##7???<=?0#1(##7???<=?1#1(##7???<=?2#1(##7???<=?3#1(##7???<=?4#1(##7???<=?5#1(##7???<=?6#1(##7???<=?7#1(##7???<>04#1(##7???<>04#4(##7???<>05#1(##7???<>06#1(##7???<>07#1(##7???<>08#4(##7???<>0<#1(##7???<>0<#4(##7???<>0=#1(##7???<>0>#1(##7???<>0?#1(##7???<>10#1(##7???<>10#4(##7???<>11#1(##7???<>12#1(##7???<>13#1(##7???<>14#4(##7???<>18#4(##7???<>1<#4(##7???<>20#4(##7???<>24#4(##7???<>28#4(##7???<>28#8(##7???<>30#8(##7???<>38#4(##7???<>38#8(##7???<>3<#4(##7???<>40#4(##7???<>40#8(##7???<>44#4(##7???<>48#4(##7???<>4<#4(##7???<>50#1(##7???<>50#4(##7???<>51#1(##7???<>52#1(##7???<>53#1(##800222:4#1(##800222:4#4(##800222:5#1(##800222:6#1(##800222:7#1(##800222:8#4(##800222:<#4(##800222;0#1(##800222;0#4(##800222;1#1(##800222;2#1(##800222;3#1(##80023714#1(##80023714#4(##80023715#1(##80023716#1(##80023717#1(##80023718#4(##8002371<#4(##80023720#4(##80023724#4(##80023728#4(##8002372<#4(##80023730#8(##80023738#8(##80023740#8(##80023748#8(##80023750#8(##80023758#8(##80023760#8(##80023768#8(##80023770#8(##80023778#8(##80023780#8(##80023788#8(##80023790#8(##80023798#8(##800237:0#8(##800237:8#8(##800237;0#8(##800237;8#8(##800237<0#8(##800237<8#8(##800237=0#8(##800237=8#8(##800237>0#8(##800237>8#8(##800237?0#8(##800237?8#8(##80023800#8(##80023808#8(##80023810#8(##80023818#8(##80023820#8(##80023828#8(##80023830#8(##80023838#8(##80023840#8(##80023848#8(##80023850#8(##80023858#8(##80023858#4(##8002385<#4(##80023860#8(##80023860#4(##80023864#4(##80023868#8(##80023868#4(##8002386<#4(##80023870#1(##80023870#4(##80023871#1(##80023872#1(##80023873#1!##693:58,4$2<'$2<#1#3?????!##6;3=93,1#!##6;3;70,8#137<74!##6;3<70,8#9>48<!##6;3;54,4#!##1?1920,1#!##6;3;68,8#!##158;:8,8#158;:8!##15=290,4#1!##160758,1#1!##15?:78,8#7???8000!##15;8:0,8#23:40!##15;8;0,1#20!##15?2=<,1#1!##15;8;0,8#20!##1?1620,8^#?#???????????????!##158=:8,8#14916<!##15;8=8,8^#?#???????????????!##15;8>0,8#23:60!##15;8?0,1#60!##15;8?0,8#60!##15;918,8^#?#???????????????!##15;920,8#23:>0!##15;930,1#20!##15;930,8#20!##15;958,8^#?#???????????????!##15;960,8#23;00!##15;970,1#60!##15;970,8#60!##15;998,8^#?#???????????????!##15;9:0,8#23;60!##15;9;0,1#20!##15;9;0,8#20!##15;9=8,8^#?#???????????????!##15;9>0,8#23;80!##15;9?0,1#40!##15;9?0,8#40!##15;:18,8^#?#???????????????!##15;:20,8#23<20!##15;:30,1#20!##15;:30,8#20!##15;:58,8^#?#???????????????!##15;:60,8#23<40!##15;:70,1#20!##15;:70,8#20!##15;:98,8^#?#???????????????!##15;::0,8#23<60!##15;:;0,1#<0!##15;:;0,8#1:<0!##15;:=8,8^#?#???????????????!##15;:>0,8#25720!##15;:?0,1#60!##15;:?0,8#=60!##15;;18,8^#?#???????????????!##15;;20,8#26480!##15;;30,1#20!##15;;30,8#20!##15;;58,8^#?#???????????????!##15;;60,8#264:0!##15;;70,1#80!##15;;70,8#80!##15;;98,8^#?#???????????????!##15;;:0,8#26520!##15;;;0,1#20!##15;;;0,8#20!##15;;=8,8^#?#???????????????!##15;;>0,8#26540!##15;;?0,1#20!##15;;?0,8#20!##15;<18,8^#?#???????????????!##15;<20,8#26560!##15;<30,1#20!##15;<30,8#20!##15;<58,8^#?#???????????????!##15;<60,8#26580!##15;<70,1#20!##15;<70,8#20!##15;<98,8^#?#???????????????!##15;<:0,8#265:0!##15;<;0,1#20!##15;<;0,8#20!##15;<=8,8^#?#???????????????!##15;<>0,8#26660!##15;<?0,1#20!##15;<?0,8#20!##15;=18,8^#?#???????????????!##15;=20,8#267>0!##15;=30,1#40!##15;=30,8#40!##15;=58,8^#?#???????????????!##15;=60,8#26820!##15;=70,1#40!##15;=70,8#40!##15;=98,8^#?#???????????????!##15;=:0,8#26860!##15;=;0,1#20!##15;=;0,8#20!##15;==8,8^#?#???????????????!##15;=>0,8#26880!##15;=?0,1#60!##15;=?0,8#60!##15;>18,8^#?#???????????????!##15;>20,8#268>0!##15;>30,1#60!##15;>30,8#60!##15;>58,8^#?#???????????????!##15;>60,8#26940!##15;>70,1#60!##15;>70,8#60!##15;>98,8^#?#???????????????!##15;>:0,8#269:0!##15;>;0,1#60!##15;>;0,8#60!##15;>=8,8^#?#???????????????!##15;>>0,8#26:00!##15;>?0,1#60!##15;>?0,8#60!##15;?18,8^#?#???????????????!##15;?20,8#26:60!##15;?30,1#60!##15;?30,8#60!##15;?58,8^#?#???????????????!##15;?60,8#26:<0!##15;?70,1#80!##15;?70,8#80!##15;?98,8^#?#???????????????!##15;?:0,8#26;40!##15;?;0,1#40!##15;?;0,8#40!##15;?=8,8^#?#???????????????!##15;?>0,8#26;80!##15;??0,1#40!##15;??0,8#40!##15<018,8^#?#???????????????!##15<020,8#26;<0!##15<030,1#60!##15<030,8#60!##15<058,8^#?#???????????????!##15<060,8#26<20!##15<070,1#60!##15<070,8#60!##15<098,8^#?#???????????????!##15<0:0,8#26<80!##15<0;0,1#60!##15<0;0,8#60!##15<0=8,8^#?#???????????????!##15<0>0,8#26<>0!##15<0?0,1#60!##15<0?0,8#60!##15<118,8^#?#???????????????!##15<120,8#26=40!##15<130,1#60!##15<130,8#60!##15<158,8^#?#???????????????!##15<160,8#26=:0!##15<170,1#60!##15<170,8#60!##15<198,8^#?#???????????????!##15<1:0,8#26>00!##15<1;0,1#20!##15<1;0,8#20!##15<1=8,8^#?#???????????????!##15<1>0,8#26?40!##15<1?0,1#20!##15<1?0,8#20!##15<218,8^#?#???????????????!##15<220,8#26?60!##15<230,1#20!##15<230,8#20!##15<258,8^#?#???????????????!##15<260,8#26?80!##15<270,1#20!##15<270,8#20!##15<298,8^#?#???????????????!##15<2:0,8#26?:0!##15<2;0,1#20!##15<2;0,8#20!##15<2=8,8^#?#???????????????!##15<2>0,8#27020!##15<2?0,1#60!##15<2?0,8#60!##15<318,8^#?#???????????????!##15<320,8#27080!##15<330,1#20!##15<330,8#220!##15<358,8^#?#???????????????!##15<360,8#151520!##15<370,1#80!##15<370,8#80!##15<398,8^#?#???????????????!##6;4308,8#!##15;868,8#15;780!##15;80<,4#????????!##15;7:8,8#!##15;7;8,8#!##15;788,8#!##15;790,8#!##15;778,8#15;690!##15;71<,4#????????!##15;6;8,8#!##15;6<8,8#!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#!##15;5=8,8#!##15;5:8,8#!##15;5;0,8#,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1276376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_572cde.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1277128 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_572cde.IT BndT_Na_001.SegItab_Na_572cde.IT_sound BF NX0 BR XSTEP F0 PSS plan 1277128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpXe.

Module LibSegNa_dpXm.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_572cde.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_572cde.IT.
Definition ENDS : list Z := [1276376].
Definition STOPS1 : list Z := [1276376] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; ELit 6896384; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",335'$2#7???7?811000#800000000000&$2#10($2-140#140,$2-140#140%#10000#158000(##15<3<0#8(##15<410#1(##15=330#8(##6;3;50#1(##6;3;58#4(##6;3;60#8(##6;3=70#4(##7???<748#1(##7???<749#1(##7???<74:#1(##7???<74;#1(##7???<74<#1(##7???<74<#4(##7???<74=#1(##7???<74>#1(##7???<74?#1(##7???<750#4(##7???<754#1(##7???<754#4(##7???<755#1(##7???<756#1(##7???<757#1(##7???<75<#1(##7???<75=#1(##7???<75>#1(##7???<75?#1(##7???<760#1(##7???<760#4(##7???<761#1(##7???<762#1(##7???<763#1(##7???<764#4(##7???<768#1(##7???<768#4(##7???<769#1(##7???<76:#1(##7???<76;#1(##7???<76<#1(##7???<76=#1(##7???<76>#1(##7???<76?#1(##7???<770#1(##7???<771#1(##7???<772#1(##7???<773#1(##7???<774#1(##7???<775#1(##7???<776#1(##7???<777#1(##7???<784#1(##7???<785#1(##7???<786#1(##7???<787#1(##7???<788#1(##7???<789#1(##7???<78:#1(##7???<78;#1(##7???<78<#1(##7???<78<#4(##7???<78=#1(##7???<78>#1(##7???<78?#1(##7???<790#4(##7???<794#4(##7???<798#4(##7???<79<#4(##7???<7:0#4(##7???<7:4#4(##7???<7:8#8(##7???<7;0#8(##7???<7;8#8(##7???<7<0#8(##7???<7<8#8(##7???<7=0#8(##7???<7=8#8(##7???<7>0#8(##7???<7>8#8(##7???<7?0#8(##7???<7?8#8(##7???<800#8(##7???<808#8(##7???<810#8(##7???<818#8(##7???<820#8(##7???<828#8(##7???<830#8(##7???<838#8(##7???<840#8(##7???<848#8(##7???<850#8(##7???<858#8(##7???<860#8(##7???<868#8(##7???<870#8(##7???<878#8(##7???<880#8(##7???<888#8(##7???<890#8(##7???<898#8(##7???<8:0#8(##7???<8:8#8(##7???<8;0#8(##7???<8;8#8(##7???<8<0#8(##7???<8<8#8(##7???<8=0#8(##7???<8=8#8(##7???<8>0#8(##7???<8>8#8(##7???<8?0#8(##7???<8?8#8(##7???<900#8(##7???<908#8(##7???<910#8(##7???<918#8(##7???<920#8(##7???<928#8(##7???<930#8(##7???<938#8(##7???<940#8(##7???<948#8(##7???<950#8(##7???<958#8(##7???<960#8(##7???<968#8(##7???<970#8(##7???<978#8(##7???<980#8(##7???<988#8(##7???<990#8(##7???<998#8(##7???<9:0#8(##7???<9:8#8(##7???<9;0#8(##7???<9;8#8(##7???<9<0#8(##7???<9<8#8(##7???<9=0#8(##7???<9=8#8(##7???<9>0#8(##7???<9>8#8(##7???<9?0#8(##7???<9?8#8(##7???<:00#8(##7???<:08#8(##7???<:10#8(##7???<:18#8(##7???<:20#8(##7???<:28#8(##7???<:30#8(##7???<:38#8(##7???<:40#8(##7???<:48#8(##7???<:50#8(##7???<:58#8(##7???<:60#8(##7???<:68#8(##7???<:70#8(##7???<:78#8(##7???<:80#8(##7???<:88#8(##7???<:90#8(##7???<:98#8(##7???<::0#8(##7???<::8#8(##7???<:;0#8(##7???<:;8#8(##7???<:<0#8(##7???<:<8#4(##7???<:<<#4(##7???<:=0#4(##7???<:=4#4(##7???<:=8#4(##7???<:=<#4(##7???<:>0#1(##7???<:>0#4(##7???<:>1#1(##7???<:>2#1(##7???<:>3#1(##7???<:>4#1(##7???<:>4#4(##7???<:>5#1(##7???<:>6#1(##7???<:>7#1(##7???<:>8#4(##7???<:><#4(##7???<:?0#4(##7???<:?4#4(##7???<:?8#4(##7???<:?<#4(##7???<;00#8(##7???<;08#8(##7???<;10#8(##7???<;18#8(##7???<;20#8(##7???<;28#8(##7???<;30#8(##7???<;38#8(##7???<;40#8(##7???<;48#8(##7???<;50#8(##7???<;58#8(##7???<;60#8(##7???<;68#8(##7???<;70#8(##7???<;78#8(##7???<;80#8(##7???<;88#8(##7???<;90#8(##7???<;98#8(##7???<;:0#8(##7???<;:8#8(##7???<;;0#8(##7???<;;8#8(##7???<;<0#8(##7???<;<8#8(##7???<;=0#8(##7???<;=8#8(##7???<;>0#8(##7???<;>8#8(##7???<;?0#8(##7???<;?8#8(##7???<<00#8(##7???<<08#8(##7???<<10#8(##7???<<18#8(##7???<<20#8(##7???<<28#8(##7???<<30#8(##7???<<38#8(##7???<<40#8(##7???<<48#8(##7???<<50#8(##7???<<58#8(##7???<<60#8(##7???<<68#8(##7???<<70#8(##7???<<74#4(##7???<<78#4(##7???<<78#8(##7???<<7<#4(##7???<<80#4(##7???<<84#4(##7???<<88#4(##7???<<8<#1(##7???<<8<#4(##7???<<8=#1(##7???<<8>#1(##7???<<8?#1(##7???<<90#1(##7???<<91#1(##7???<<92#1(##7???<<93#1(##7???<<94#1(##7???<<94#4(##7???<<95#1(##7???<<96#1(##7???<<97#1(##7???<<98#4(##7???<<9<#4(##7???<<:0#1(##7???<<:0#4(##7???<<:1#1(##7???<<:2#1(##7???<<:3#1(##7???<<:4#1(##7???<<:5#1(##7???<<:6#1(##7???<<:7#1(##7???<<:8#1(##7???<<:9#1(##7???<<::#1(##7???<<:;#1(##7???<<:<#1(##7???<<:=#1(##7???<<:>#1(##7???<<:?#1(##7???<<;0#1(##7???<<;1#1(##7???<<;2#1(##7???<<;3#1(##7???<<;4#1(##7???<<;5#1(##7???<<;6#1(##7???<<;7#1(##7???<<<<#1(##7???<<<=#1(##7???<<<>#1(##7???<<<?#1(##7???<<?<#1(##7???<<?=#1(##7???<<?>#1(##7???<<??#1(##7???<=00#1(##7???<=01#1(##7???<=02#1(##7???<=03#1(##7???<=04#1(##7???<=05#1(##7???<=06#1(##7???<=07#1(##7???<=08#1(##7???<=09#1(##7???<=0:#1(##7???<=0;#1(##7???<=0<#1(##7???<=0=#1(##7???<=0>#1(##7???<=0?#1(##7???<=10#1(##7???<=10#4(##7???<=11#1(##7???<=12#1(##7???<=13#1(##7???<=14#4(##7???<=18#1(##7???<=18#4(##7???<=19#1(##7???<=1:#1(##7???<=1;#1(##7???<=1<#1(##7???<=1<#4(##7???<=1=#1(##7???<=1>#1(##7???<=1?#1(##7???<=20#4(##7???<=24#1(##7???<=24#4(##7???<=25#1(##7???<=26#1(##7???<=27#1(##7???<=28#1(##7???<=28#4(##7???<=29#1(##7???<=2:#1(##7???<=2;#1(##7???<=2<#4(##7???<=30#1(##7???<=30#4(##7???<=31#1(##7???<=32#1(##7???<=33#1(##7???<=34#1(##7???<=34#4(##7???<=35#1(##7???<=36#1(##7???<=37#1(##7???<=38#4(##7???<=3<#1(##7???<=3<#4(##7???<=3=#1(##7???<=3>#1(##7???<=3?#1(##7???<=40#1(##7???<=40#4(##7???<=41#1(##7???<=42#1(##7???<=43#1(##7???<=44#4(##7???<=48#1(##7???<=48#4(##7???<=49#1(##7???<=4:#1(##7???<=4;#1(##7???<=4<#1(##7???<=4<#4(##7???<=4=#1(##7???<=4>#1(##7???<=4?#1(##7???<=50#4(##7???<=54#1(##7???<=54#4(##7???<=55#1(##7???<=56#1(##7???<=57#1(##7???<=58#1(##7???<=58#4(##7???<=59#1(##7???<=5:#1(##7???<=5;#1(##7???<=5<#4(##7???<=60#4(##7???<=64#1(##7???<=64#4(##7???<=65#1(##7???<=66#1(##7???<=67#1(##7???<=68#1(##7???<=69#1(##7???<=6:#1(##7???<=6;#1(##7???<=6<#1(##7???<=6=#1(##7???<=6>#1(##7???<=6?#1(##7???<=70#1(##7???<=71#1(##7???<=72#1(##7???<=73#1(##7???<=74#1(##7???<=75#1(##7???<=76#1(##7???<=77#1(##7???<=78#1(##7???<=78#4(##7???<=79#1(##7???<=7:#1(##7???<=7;#1(##7???<=7<#4(##7???<=80#1(##7???<=80#4(##7???<=81#1(##7???<=82#1(##7???<=83#1(##7???<=84#1(##7???<=84#4(##7???<=85#1(##7???<=86#1(##7???<=87#1(##7???<=88#4(##7???<=8<#1(##7???<=8<#4(##7???<=8=#1(##7???<=8>#1(##7???<=8?#1(##7???<=90#1(##7???<=90#4(##7???<=91#1(##7???<=92#1(##7???<=93#1(##7???<=94#4(##7???<=98#1(##7???<=98#4(##7???<=99#1(##7???<=9:#1(##7???<=9;#1(##7???<=9<#1(##7???<=9<#4(##7???<=9=#1(##7???<=9>#1(##7???<=9?#1(##7???<=:0#4(##7???<=:4#1(##7???<=:4#4(##7???<=:5#1(##7???<=:6#1(##7???<=:7#1(##7???<=:8#1(##7???<=:8#4(##7???<=:9#1(##7???<=::#1(##7???<=:;#1(##7???<=:<#4(##7???<=;0#1(##7???<=;0#4(##7???<=;1#1(##7???<=;2#1(##7???<=;3#1(##7???<=;4#1(##7???<=;4#4(##7???<=;5#1(##7???<=;6#1(##7???<=;7#1(##7???<=;8#4(##7???<=;<#1(##7???<=;<#4(##7???<=;=#1(##7???<=;>#1(##7???<=;?#1(##7???<=<0#1(##7???<=<1#1(##7???<=<2#1(##7???<=<3#1(##7???<=>8#1(##7???<=>9#1(##7???<=>:#1(##7???<=>;#1(##7???<=><#1(##7???<=>=#1(##7???<=>>#1(##7???<=>?#1(##7???<=?0#1(##7???<=?1#1(##7???<=?2#1(##7???<=?3#1(##7???<=?4#1(##7???<=?5#1(##7???<=?6#1(##7???<=?7#1(##7???<>04#1(##7???<>04#4(##7???<>05#1(##7???<>06#1(##7???<>07#1(##7???<>08#4(##7???<>0<#1(##7???<>0<#4(##7???<>0=#1(##7???<>0>#1(##7???<>0?#1(##7???<>10#1(##7???<>10#4(##7???<>11#1(##7???<>12#1(##7???<>13#1(##7???<>14#4(##7???<>18#4(##7???<>1<#4(##7???<>20#4(##7???<>24#4(##7???<>28#4(##7???<>28#8(##7???<>30#8(##7???<>38#4(##7???<>38#8(##7???<>3<#4(##7???<>40#4(##7???<>40#8(##7???<>44#4(##7???<>48#4(##7???<>4<#4(##7???<>50#1(##7???<>50#4(##7???<>51#1(##7???<>52#1(##7???<>53#1(##800222:4#1(##800222:4#4(##800222:5#1(##800222:6#1(##800222:7#1(##800222:8#4(##800222:<#4(##800222;0#1(##800222;0#4(##800222;1#1(##800222;2#1(##800222;3#1(##80023714#1(##80023714#4(##80023715#1(##80023716#1(##80023717#1(##80023718#4(##8002371<#4(##80023720#4(##80023724#4(##80023728#4(##8002372<#4(##80023730#8(##80023738#8(##80023740#8(##80023748#8(##80023750#8(##80023758#8(##80023760#8(##80023768#8(##80023770#8(##80023778#8(##80023780#8(##80023788#8(##80023790#8(##80023798#8(##800237:0#8(##800237:8#8(##800237;0#8(##800237;8#8(##800237<0#8(##800237<8#8(##800237=0#8(##800237=8#8(##800237>0#8(##800237>8#8(##800237?0#8(##800237?8#8(##80023800#8(##80023808#8(##80023810#8(##80023818#8(##80023820#8(##80023828#8(##80023830#8(##80023838#8(##80023840#8(##80023848#8(##80023850#8(##80023858#8(##80023858#4(##8002385<#4(##80023860#8(##80023860#4(##80023864#4(##80023868#8(##80023868#4(##8002386<#4(##80023870#1(##80023870#4(##80023871#1(##80023872#1(##80023873#1!##693:58,4$2<'$2<#1#3?????!##6;3=70,4#!##6;3=93,1#!##6;3;60,8#6;3;68!##6;3;58,4#1!##6;3;70,8#137<74!##6;3<70,8#9>48<!##6;3;54,4#!##1?1920,1#!##6;3;68,8#!##15<410,1#!##158;:8,8#158;:8!##15<3<0,8#1!##15=290,4#1!##15=330,8#!##160758,1#1!##15?:78,8#7???8000!##15;8:0,8#23:40!##15;8;0,1#20!##15?2=<,1#1!##15;8;0,8#20!##1?1620,8^#?#???????????????!##158=:8,8#14916<!##15;8=8,8^#?#???????????????!##15;8>0,8#23:60!##15;8?0,1#60!##15;8?0,8#60!##15;918,8^#?#???????????????!##15;920,8#23:>0!##15;930,1#20!##15;930,8#20!##15;958,8^#?#???????????????!##15;960,8#23;00!##15;970,1#60!##15;970,8#60!##15;998,8^#?#???????????????!##15;9:0,8#23;60!##15;9;0,1#20!##15;9;0,8#20!##15;9=8,8^#?#???????????????!##15;9>0,8#23;80!##15;9?0,1#40!##15;9?0,8#40!##15;:18,8^#?#???????????????!##15;:20,8#23<20!##15;:30,1#20!##15;:30,8#20!##15;:58,8^#?#???????????????!##15;:60,8#23<40!##15;:70,1#20!##15;:70,8#20!##15;:98,8^#?#???????????????!##15;::0,8#23<60!##15;:;0,1#<0!##15;:;0,8#1:<0!##15;:=8,8^#?#???????????????!##15;:>0,8#25720!##15;:?0,1#60!##15;:?0,8#=60!##15;;18,8^#?#???????????????!##15;;20,8#26480!##15;;30,1#20!##15;;30,8#20!##15;;58,8^#?#???????????????!##15;;60,8#264:0!##15;;70,1#80!##15;;70,8#80!##15;;98,8^#?#???????????????!##15;;:0,8#26520!##15;;;0,1#20!##15;;;0,8#20!##15;;=8,8^#?#???????????????!##15;;>0,8#26540!##15;;?0,1#20!##15;;?0,8#20!##15;<18,8^#?#???????????????!##15;<20,8#26560!##15;<30,1#20!##15;<30,8#20!##15;<58,8^#?#???????????????!##15;<60,8#26580!##15;<70,1#20!##15;<70,8#20!##15;<98,8^#?#???????????????!##15;<:0,8#265:0!##15;<;0,1#20!##15;<;0,8#20!##15;<=8,8^#?#???????????????!##15;<>0,8#26660!##15;<?0,1#20!##15;<?0,8#20!##15;=18,8^#?#???????????????!##15;=20,8#267>0!##15;=30,1#40!##15;=30,8#40!##15;=58,8^#?#???????????????!##15;=60,8#26820!##15;=70,1#40!##15;=70,8#40!##15;=98,8^#?#???????????????!##15;=:0,8#26860!##15;=;0,1#20!##15;=;0,8#20!##15;==8,8^#?#???????????????!##15;=>0,8#26880!##15;=?0,1#60!##15;=?0,8#60!##15;>18,8^#?#???????????????!##15;>20,8#268>0!##15;>30,1#60!##15;>30,8#60!##15;>58,8^#?#???????????????!##15;>60,8#26940!##15;>70,1#60!##15;>70,8#60!##15;>98,8^#?#???????????????!##15;>:0,8#269:0!##15;>;0,1#60!##15;>;0,8#60!##15;>=8,8^#?#???????????????!##15;>>0,8#26:00!##15;>?0,1#60!##15;>?0,8#60!##15;?18,8^#?#???????????????!##15;?20,8#26:60!##15;?30,1#60!##15;?30,8#60!##15;?58,8^#?#???????????????!##15;?60,8#26:<0!##15;?70,1#80!##15;?70,8#80!##15;?98,8^#?#???????????????!##15;?:0,8#26;40!##15;?;0,1#40!##15;?;0,8#40!##15;?=8,8^#?#???????????????!##15;?>0,8#26;80!##15;??0,1#40!##15;??0,8#40!##15<018,8^#?#???????????????!##15<020,8#26;<0!##15<030,1#60!##15<030,8#60!##15<058,8^#?#???????????????!##15<060,8#26<20!##15<070,1#60!##15<070,8#60!##15<098,8^#?#???????????????!##15<0:0,8#26<80!##15<0;0,1#60!##15<0;0,8#60!##15<0=8,8^#?#???????????????!##15<0>0,8#26<>0!##15<0?0,1#60!##15<0?0,8#60!##15<118,8^#?#???????????????!##15<120,8#26=40!##15<130,1#60!##15<130,8#60!##15<158,8^#?#???????????????!##15<160,8#26=:0!##15<170,1#60!##15<170,8#60!##15<198,8^#?#???????????????!##15<1:0,8#26>00!##15<1;0,1#20!##15<1;0,8#20!##15<1=8,8^#?#???????????????!##15<1>0,8#26?40!##15<1?0,1#20!##15<1?0,8#20!##15<218,8^#?#???????????????!##15<220,8#26?60!##15<230,1#20!##15<230,8#20!##15<258,8^#?#???????????????!##15<260,8#26?80!##15<270,1#20!##15<270,8#20!##15<298,8^#?#???????????????!##15<2:0,8#26?:0!##15<2;0,1#20!##15<2;0,8#20!##15<2=8,8^#?#???????????????!##15<2>0,8#27020!##15<2?0,1#60!##15<2?0,8#60!##15<318,8^#?#???????????????!##15<320,8#27080!##15<330,1#20!##15<330,8#220!##15<358,8^#?#???????????????!##15<360,8#151520!##15<370,1#80!##15<370,8#80!##15<398,8^#?#???????????????!##6;4308,8#!##15;868,8#15;780!##15;80<,4#????????!##15;7:8,8#!##15;7;8,8#!##15;788,8#!##15;790,8#!##15;778,8#15;690!##15;71<,4#????????!##15;6;8,8#!##15;6<8,8#!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#6;4318!##15;5=8,8#6;4318!##15;5:8,8#!##15;5;0,8#"%pstring).
Definition ss0 : sym_state := SS 1277128 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",259$2-140#140##15<3<0#8##15<410#1##15=330#8##6;3;50#1##6;3;58#4##6;3;60#8##6;3=70#4##7???<748#1##7???<749#1##7???<74:#1##7???<74;#1##7???<74<#1##7???<74<#4##7???<74=#1##7???<74>#1##7???<74?#1##7???<750#4##7???<754#1##7???<754#4##7???<755#1##7???<756#1##7???<757#1##7???<75<#1##7???<75=#1##7???<75>#1##7???<75?#1##7???<760#1##7???<760#4##7???<761#1##7???<762#1##7???<763#1##7???<764#4##7???<768#1##7???<768#4##7???<769#1##7???<76:#1##7???<76;#1##7???<76<#1##7???<76=#1##7???<76>#1##7???<76?#1##7???<770#1##7???<771#1##7???<772#1##7???<773#1##7???<774#1##7???<775#1##7???<776#1##7???<777#1##7???<784#1##7???<785#1##7???<786#1##7???<787#1##7???<788#1##7???<789#1##7???<78:#1##7???<78;#1##7???<78<#1##7???<78<#4##7???<78=#1##7???<78>#1##7???<78?#1##7???<790#4##7???<794#4##7???<798#4##7???<79<#4##7???<7:0#4##7???<7:4#4##7???<7:8#8##7???<7;0#8##7???<7;8#8##7???<7<0#8##7???<7<8#8##7???<7=0#8##7???<7=8#8##7???<7>0#8##7???<7>8#8##7???<7?0#8##7???<7?8#8##7???<800#8##7???<808#8##7???<810#8##7???<818#8##7???<820#8##7???<828#8##7???<830#8##7???<838#8##7???<840#8##7???<848#8##7???<850#8##7???<858#8##7???<860#8##7???<868#8##7???<870#8##7???<878#8##7???<880#8##7???<888#8##7???<890#8##7???<898#8##7???<8:0#8##7???<8:8#8##7???<8;0#8##7???<8;8#8##7???<8<0#8##7???<8<8#8##7???<8=0#8##7???<8=8#8##7???<8>0#8##7???<8>8#8##7???<8?0#8##7???<8?8#8##7???<900#8##7???<908#8##7???<910#8##7???<918#8##7???<920#8##7???<928#8##7???<930#8##7???<938#8##7???<940#8##7???<948#8##7???<950#8##7???<958#8##7???<960#8##7???<968#8##7???<970#8##7???<978#8##7???<980#8##7???<988#8##7???<990#8##7???<998#8##7???<9:0#8##7???<9:8#8##7???<9;0#8##7???<9;8#8##7???<9<0#8##7???<9<8#8##7???<9=0#8##7???<9=8#8##7???<9>0#8##7???<9>8#8##7???<9?0#8##7???<9?8#8##7???<:00#8##7???<:08#8##7???<:10#8##7???<:18#8##7???<:20#8##7???<:28#8##7???<:30#8##7???<:38#8##7???<:40#8##7???<:48#8##7???<:50#8##7???<:58#8##7???<:60#8##7???<:68#8##7???<:70#8##7???<:78#8##7???<:80#8##7???<:88#8##7???<:90#8##7???<:98#8##7???<::0#8##7???<::8#8##7???<:;0#8##7???<:;8#8##7???<:<0#8##7???<:<8#4##7???<:<<#4##7???<:=0#4##7???<:=4#4##7???<:=8#4##7???<:=<#4##7???<:>0#1##7???<:>0#4##7???<:>1#1##7???<:>2#1##7???<:>3#1##7???<:>4#1##7???<:>4#4##7???<:>5#1##7???<:>6#1##7???<:>7#1##7???<:>8#4##7???<:><#4##7???<:?0#4##7???<:?4#4##7???<:?8#4##7???<:?<#4##7???<;00#8##7???<;08#8##7???<;10#8##7???<;18#8##7???<;20#8##7???<;28#8##7???<;30#8##7???<;38#8##7???<;40#8##7???<;48#8##7???<;50#8##7???<;58#8##7???<;60#8##7???<;68#8##7???<;70#8##7???<;78#8##7???<;80#8##7???<;88#8##7???<;90#8##7???<;98#8##7???<;:0#8##7???<;:8#8##7???<;;0#8##7???<;;8#8##7???<;<0#8##7???<;<8#8##7???<;=0#8##7???<;=8#8##7???<;>0#8##7???<;>8#8##7???<;?0#8##7???<;?8#8##7???<<00#8##7???<<08#8##7???<<10#8##7???<<18#8##7???<<20#8##7???<<28#8##7???<<30#8##7???<<38#8##7???<<40#8##7???<<48#8##7???<<50#8##7???<<58#8##7???<<60#8##7???<<68#8##7???<<70#8##7???<<74#4##7???<<78#4##7???<<78#8##7???<<7<#4##7???<<80#4##7???<<84#4##7???<<88#4##7???<<8<#1##7???<<8<#4##7???<<8=#1##7???<<8>#1##7???<<8?#1##7???<<90#1##7???<<91#1##7???<<92#1##7???<<93#1##7???<<94#1##7???<<94#4##7???<<95#1##7???<<96#1##7???<<97#1##7???<<98#4##7???<<9<#4##7???<<:0#1##7???<<:0#4##7???<<:1#1##7???<<:2#1##7???<<:3#1##7???<<:4#1##7???<<:5#1##7???<<:6#1##7???<<:7#1##7???<<:8#1##7???<<:9#1##7???<<::#1##7???<<:;#1##7???<<:<#1##7???<<:=#1##7???<<:>#1##7???<<:?#1##7???<<;0#1##7???<<;1#1##7???<<;2#1##7???<<;3#1##7???<<;4#1##7???<<;5#1##7???<<;6#1##7???<<;7#1##7???<<<<#1##7???<<<=#1##7???<<<>#1##7???<<<?#1##7???<<?<#1##7???<<?=#1##7???<<?>#1##7???<<??#1##7???<=00#1##7???<=01#1##7???<=02#1##7???<=03#1##7???<=04#1##7???<=05#1##7???<=06#1##7???<=07#1##7???<=08#1##7???<=09#1##7???<=0:#1##7???<=0;#1##7???<=0<#1##7???<=0=#1##7???<=0>#1##7???<=0?#1##7???<=10#1##7???<=10#4##7???<=11#1##7???<=12#1##7???<=13#1##7???<=14#4##7???<=18#1##7???<=18#4##7???<=19#1##7???<=1:#1##7???<=1;#1##7???<=1<#1##7???<=1<#4##7???<=1=#1##7???<=1>#1##7???<=1?#1##7???<=20#4##7???<=24#1##7???<=24#4##7???<=25#1##7???<=26#1##7???<=27#1##7???<=28#1##7???<=28#4##7???<=29#1##7???<=2:#1##7???<=2;#1##7???<=2<#4##7???<=30#1##7???<=30#4##7???<=31#1##7???<=32#1##7???<=33#1##7???<=34#1##7???<=34#4##7???<=35#1##7???<=36#1##7???<=37#1##7???<=38#4##7???<=3<#1##7???<=3<#4##7???<=3=#1##7???<=3>#1##7???<=3?#1##7???<=40#1##7???<=40#4##7???<=41#1##7???<=42#1##7???<=43#1##7???<=44#4##7???<=48#1##7???<=48#4##7???<=49#1##7???<=4:#1##7???<=4;#1##7???<=4<#1##7???<=4<#4##7???<=4=#1##7???<=4>#1##7???<=4?#1##7???<=50#4##7???<=54#1##7???<=54#4##7???<=55#1##7???<=56#1##7???<=57#1##7???<=58#1##7???<=58#4##7???<=59#1##7???<=5:#1##7???<=5;#1##7???<=5<#4##7???<=60#4##7???<=64#1##7???<=64#4##7???<=65#1##7???<=66#1##7???<=67#1##7???<=68#1##7???<=69#1##7???<=6:#1##7???<=6;#1##7???<=6<#1##7???<=6=#1##7???<=6>#1##7???<=6?#1##7???<=70#1##7???<=71#1##7???<=72#1##7???<=73#1##7???<=74#1##7???<=75#1##7???<=76#1##7???<=77#1##7???<=78#1##7???<=78#4##7???<=79#1##7???<=7:#1##7???<=7;#1##7???<=7<#4##7???<=80#1##7???<=80#4##7???<=81#1##7???<=82#1##7???<=83#1##7???<=84#1##7???<=84#4##7???<=85#1##7???<=86#1##7???<=87#1##7???<=88#4##7???<=8<#1##7???<=8<#4##7???<=8=#1##7???<=8>#1##7???<=8?#1##7???<=90#1##7???<=90#4##7???<=91#1##7???<=92#1##7???<=93#1##7???<=94#4##7???<=98#1##7???<=98#4##7???<=99#1##7???<=9:#1##7???<=9;#1##7???<=9<#1##7???<=9<#4##7???<=9=#1##7???<=9>#1##7???<=9?#1##7???<=:0#4##7???<=:4#1##7???<=:4#4##7???<=:5#1##7???<=:6#1##7???<=:7#1##7???<=:8#1##7???<=:8#4##7???<=:9#1##7???<=::#1##7???<=:;#1##7???<=:<#4##7???<=;0#1##7???<=;0#4##7???<=;1#1##7???<=;2#1##7???<=;3#1##7???<=;4#1##7???<=;4#4##7???<=;5#1##7???<=;6#1##7???<=;7#1##7???<=;8#4##7???<=;<#1##7???<=;<#4##7???<=;=#1##7???<=;>#1##7???<=;?#1##7???<=<0#1##7???<=<1#1##7???<=<2#1##7???<=<3#1##7???<=>8#1##7???<=>9#1##7???<=>:#1##7???<=>;#1##7???<=><#1##7???<=>=#1##7???<=>>#1##7???<=>?#1##7???<=?0#1##7???<=?1#1##7???<=?2#1##7???<=?3#1##7???<=?4#1##7???<=?5#1##7???<=?6#1##7???<=?7#1##7???<>04#1##7???<>04#4##7???<>05#1##7???<>06#1##7???<>07#1##7???<>08#4##7???<>0<#1##7???<>0<#4##7???<>0=#1##7???<>0>#1##7???<>0?#1##7???<>10#1##7???<>10#4##7???<>11#1##7???<>12#1##7???<>13#1##7???<>14#4##7???<>18#4##7???<>1<#4##7???<>20#4##7???<>24#4##7???<>28#4##7???<>28#8##7???<>30#8##7???<>38#4##7???<>38#8##7???<>3<#4##7???<>40#4##7???<>40#8##7???<>44#4##7???<>48#4##7???<>4<#4##7???<>50#1##7???<>50#4##7???<>51#1##7???<>52#1##7???<>53#1##800222:4#1##800222:4#4##800222:5#1##800222:6#1##800222:7#1##800222:8#4##800222:<#4##800222;0#1##800222;0#4##800222;1#1##800222;2#1##800222;3#1##80023714#1##80023714#4##80023715#1##80023716#1##80023717#1##80023718#4##8002371<#4##80023720#4##80023724#4##80023728#4##8002372<#4##80023730#8##80023738#8##80023740#8##80023748#8##80023750#8##80023758#8##80023760#8##80023768#8##80023770#8##80023778#8##80023780#8##80023788#8##80023790#8##80023798#8##800237:0#8##800237:8#8##800237;0#8##800237;8#8##800237<0#8##800237<8#8##800237=0#8##800237=8#8##800237>0#8##800237>8#8##800237?0#8##800237?8#8##80023800#8##80023808#8##80023810#8##80023818#8##80023820#8##80023828#8##80023830#8##80023838#8##80023840#8##80023848#8##80023850#8##80023858#8##80023858#4##8002385<#4##80023860#8##80023860#4##80023864#4##80023868#8##80023868#4##8002386<#4##80023870#1##80023870#4##80023871#1##80023872#1##80023873#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",259$2-140#140##15<3<0#8##15<410#1##15=330#8##6;3;50#1##6;3;58#4##6;3;60#8##6;3=70#4##7???<748#1##7???<749#1##7???<74:#1##7???<74;#1##7???<74<#1##7???<74<#4##7???<74=#1##7???<74>#1##7???<74?#1##7???<750#4##7???<754#1##7???<754#4##7???<755#1##7???<756#1##7???<757#1##7???<75<#1##7???<75=#1##7???<75>#1##7???<75?#1##7???<760#1##7???<760#4##7???<761#1##7???<762#1##7???<763#1##7???<764#4##7???<768#1##7???<768#4##7???<769#1##7???<76:#1##7???<76;#1##7???<76<#1##7???<76=#1##7???<76>#1##7???<76?#1##7???<770#1##7???<771#1##7???<772#1##7???<773#1##7???<774#1##7???<775#1##7???<776#1##7???<777#1##7???<784#1##7???<785#1##7???<786#1##7???<787#1##7???<788#1##7???<789#1##7???<78:#1##7???<78;#1##7???<78<#1##7???<78<#4##7???<78=#1##7???<78>#1##7???<78?#1##7???<790#4##7???<794#4##7???<798#4##7???<79<#4##7???<7:0#4##7???<7:4#4##7???<7:8#8##7???<7;0#8##7???<7;8#8##7???<7<0#8##7???<7<8#8##7???<7=0#8##7???<7=8#8##7???<7>0#8##7???<7>8#8##7???<7?0#8##7???<7?8#8##7???<800#8##7???<808#8##7???<810#8##7???<818#8##7???<820#8##7???<828#8##7???<830#8##7???<838#8##7???<840#8##7???<848#8##7???<850#8##7???<858#8##7???<860#8##7???<868#8##7???<870#8##7???<878#8##7???<880#8##7???<888#8##7???<890#8##7???<898#8##7???<8:0#8##7???<8:8#8##7???<8;0#8##7???<8;8#8##7???<8<0#8##7???<8<8#8##7???<8=0#8##7???<8=8#8##7???<8>0#8##7???<8>8#8##7???<8?0#8##7???<8?8#8##7???<900#8##7???<908#8##7???<910#8##7???<918#8##7???<920#8##7???<928#8##7???<930#8##7???<938#8##7???<940#8##7???<948#8##7???<950#8##7???<958#8##7???<960#8##7???<968#8##7???<970#8##7???<978#8##7???<980#8##7???<988#8##7???<990#8##7???<998#8##7???<9:0#8##7???<9:8#8##7???<9;0#8##7???<9;8#8##7???<9<0#8##7???<9<8#8##7???<9=0#8##7???<9=8#8##7???<9>0#8##7???<9>8#8##7???<9?0#8##7???<9?8#8##7???<:00#8##7???<:08#8##7???<:10#8##7???<:18#8##7???<:20#8##7???<:28#8##7???<:30#8##7???<:38#8##7???<:40#8##7???<:48#8##7???<:50#8##7???<:58#8##7???<:60#8##7???<:68#8##7???<:70#8##7???<:78#8##7???<:80#8##7???<:88#8##7???<:90#8##7???<:98#8##7???<::0#8##7???<::8#8##7???<:;0#8##7???<:;8#8##7???<:<0#8##7???<:<8#4##7???<:<<#4##7???<:=0#4##7???<:=4#4##7???<:=8#4##7???<:=<#4##7???<:>0#1##7???<:>0#4##7???<:>1#1##7???<:>2#1##7???<:>3#1##7???<:>4#1##7???<:>4#4##7???<:>5#1##7???<:>6#1##7???<:>7#1##7???<:>8#4##7???<:><#4##7???<:?0#4##7???<:?4#4##7???<:?8#4##7???<:?<#4##7???<;00#8##7???<;08#8##7???<;10#8##7???<;18#8##7???<;20#8##7???<;28#8##7???<;30#8##7???<;38#8##7???<;40#8##7???<;48#8##7???<;50#8##7???<;58#8##7???<;60#8##7???<;68#8##7???<;70#8##7???<;78#8##7???<;80#8##7???<;88#8##7???<;90#8##7???<;98#8##7???<;:0#8##7???<;:8#8##7???<;;0#8##7???<;;8#8##7???<;<0#8##7???<;<8#8##7???<;=0#8##7???<;=8#8##7???<;>0#8##7???<;>8#8##7???<;?0#8##7???<;?8#8##7???<<00#8##7???<<08#8##7???<<10#8##7???<<18#8##7???<<20#8##7???<<28#8##7???<<30#8##7???<<38#8##7???<<40#8##7???<<48#8##7???<<50#8##7???<<58#8##7???<<60#8##7???<<68#8##7???<<70#8##7???<<74#4##7???<<78#4##7???<<78#8##7???<<7<#4##7???<<80#4##7???<<84#4##7???<<88#4##7???<<8<#1##7???<<8<#4##7???<<8=#1##7???<<8>#1##7???<<8?#1##7???<<90#1##7???<<91#1##7???<<92#1##7???<<93#1##7???<<94#1##7???<<94#4##7???<<95#1##7???<<96#1##7???<<97#1##7???<<98#4##7???<<9<#4##7???<<:0#1##7???<<:0#4##7???<<:1#1##7???<<:2#1##7???<<:3#1##7???<<:4#1##7???<<:5#1##7???<<:6#1##7???<<:7#1##7???<<:8#1##7???<<:9#1##7???<<::#1##7???<<:;#1##7???<<:<#1##7???<<:=#1##7???<<:>#1##7???<<:?#1##7???<<;0#1##7???<<;1#1##7???<<;2#1##7???<<;3#1##7???<<;4#1##7???<<;5#1##7???<<;6#1##7???<<;7#1##7???<<<<#1##7???<<<=#1##7???<<<>#1##7???<<<?#1##7???<<?<#1##7???<<?=#1##7???<<?>#1##7???<<??#1##7???<=00#1##7???<=01#1##7???<=02#1##7???<=03#1##7???<=04#1##7???<=05#1##7???<=06#1##7???<=07#1##7???<=08#1##7???<=09#1##7???<=0:#1##7???<=0;#1##7???<=0<#1##7???<=0=#1##7???<=0>#1##7???<=0?#1##7???<=10#1##7???<=10#4##7???<=11#1##7???<=12#1##7???<=13#1##7???<=14#4##7???<=18#1##7???<=18#4##7???<=19#1##7???<=1:#1##7???<=1;#1##7???<=1<#1##7???<=1<#4##7???<=1=#1##7???<=1>#1##7???<=1?#1##7???<=20#4##7???<=24#1##7???<=24#4##7???<=25#1##7???<=26#1##7???<=27#1##7???<=28#1##7???<=28#4##7???<=29#1##7???<=2:#1##7???<=2;#1##7???<=2<#4##7???<=30#1##7???<=30#4##7???<=31#1##7???<=32#1##7???<=33#1##7???<=34#1##7???<=34#4##7???<=35#1##7???<=36#1##7???<=37#1##7???<=38#4##7???<=3<#1##7???<=3<#4##7???<=3=#1##7???<=3>#1##7???<=3?#1##7???<=40#1##7???<=40#4##7???<=41#1##7???<=42#1##7???<=43#1##7???<=44#4##7???<=48#1##7???<=48#4##7???<=49#1##7???<=4:#1##7???<=4;#1##7???<=4<#1##7???<=4<#4##7???<=4=#1##7???<=4>#1##7???<=4?#1##7???<=50#4##7???<=54#1##7???<=54#4##7???<=55#1##7???<=56#1##7???<=57#1##7???<=58#1##7???<=58#4##7???<=59#1##7???<=5:#1##7???<=5;#1##7???<=5<#4##7???<=60#4##7???<=64#1##7???<=64#4##7???<=65#1##7???<=66#1##7???<=67#1##7???<=68#1##7???<=69#1##7???<=6:#1##7???<=6;#1##7???<=6<#1##7???<=6=#1##7???<=6>#1##7???<=6?#1##7???<=70#1##7???<=71#1##7???<=72#1##7???<=73#1##7???<=74#1##7???<=75#1##7???<=76#1##7???<=77#1##7???<=78#1##7???<=78#4##7???<=79#1##7???<=7:#1##7???<=7;#1##7???<=7<#4##7???<=80#1##7???<=80#4##7???<=81#1##7???<=82#1##7???<=83#1##7???<=84#1##7???<=84#4##7???<=85#1##7???<=86#1##7???<=87#1##7???<=88#4##7???<=8<#1##7???<=8<#4##7???<=8=#1##7???<=8>#1##7???<=8?#1##7???<=90#1##7???<=90#4##7???<=91#1##7???<=92#1##7???<=93#1##7???<=94#4##7???<=98#1##7???<=98#4##7???<=99#1##7???<=9:#1##7???<=9;#1##7???<=9<#1##7???<=9<#4##7???<=9=#1##7???<=9>#1##7???<=9?#1##7???<=:0#4##7???<=:4#1##7???<=:4#4##7???<=:5#1##7???<=:6#1##7???<=:7#1##7???<=:8#1##7???<=:8#4##7???<=:9#1##7???<=::#1##7???<=:;#1##7???<=:<#4##7???<=;0#1##7???<=;0#4##7???<=;1#1##7???<=;2#1##7???<=;3#1##7???<=;4#1##7???<=;4#4##7???<=;5#1##7???<=;6#1##7???<=;7#1##7???<=;8#4##7???<=;<#1##7???<=;<#4##7???<=;=#1##7???<=;>#1##7???<=;?#1##7???<=<0#1##7???<=<1#1##7???<=<2#1##7???<=<3#1##7???<=>8#1##7???<=>9#1##7???<=>:#1##7???<=>;#1##7???<=><#1##7???<=>=#1##7???<=>>#1##7???<=>?#1##7???<=?0#1##7???<=?1#1##7???<=?2#1##7???<=?3#1##7???<=?4#1##7???<=?5#1##7???<=?6#1##7???<=?7#1##7???<>04#1##7???<>04#4##7???<>05#1##7???<>06#1##7???<>07#1##7???<>08#4##7???<>0<#1##7???<>0<#4##7???<>0=#1##7???<>0>#1##7???<>0?#1##7???<>10#1##7???<>10#4##7???<>11#1##7???<>12#1##7???<>13#1##7???<>14#4##7???<>18#4##7???<>1<#4##7???<>20#4##7???<>24#4##7???<>28#4##7???<>28#8##7???<>30#8##7???<>38#4##7???<>38#8##7???<>3<#4##7???<>40#4##7???<>40#8##7???<>44#4##7???<>48#4##7???<>4<#4##7???<>50#1##7???<>50#4##7???<>51#1##7???<>52#1##7???<>53#1##800222:4#1##800222:4#4##800222:5#1##800222:6#1##800222:7#1##800222:8#4##800222:<#4##800222;0#1##800222;0#4##800222;1#1##800222;2#1##800222;3#1##80023714#1##80023714#4##80023715#1##80023716#1##80023717#1##80023718#4##8002371<#4##80023720#4##80023724#4##80023728#4##8002372<#4##80023730#8##80023738#8##80023740#8##80023748#8##80023750#8##80023758#8##80023760#8##80023768#8##80023770#8##80023778#8##80023780#8##80023788#8##80023790#8##80023798#8##800237:0#8##800237:8#8##800237;0#8##800237;8#8##800237<0#8##800237<8#8##800237=0#8##800237=8#8##800237>0#8##800237>8#8##800237?0#8##800237?8#8##80023800#8##80023808#8##80023810#8##80023818#8##80023820#8##80023828#8##80023830#8##80023838#8##80023840#8##80023848#8##80023850#8##80023858#8##80023858#4##8002385<#4##80023860#8##80023860#4##80023864#4##80023868#8##80023868#4##8002386<#4##80023870#1##80023870#4##80023871#1##80023872#1##80023873#1"%pstring).
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#1379=8#1379=8#5=#1379=8,20##137=3<+$2-10$3#693;00#^#1##$:$9$:$:^#6##^#>#???????????????#?????0000000000^#?#?????0000000000#5>$12$13$14$15$16$17$18$19$1:$1;#15=2?0$1=$1>$1?,,4?0!$2-30,8$:!$2-28,8#13?<14!$2-20,8$:!$2-18,8#137=34!##15<3<0,8#!##15=330,8#!##80023868,8#!##80023860,8#!##80023858,8#!##80023850,8#!##80023848,8#!##80023840,8#!##80023838,8#!##80023830,8#!##80023828,8#!##80023820,8#!##80023818,8#!##80023810,8#!##80023808,8#!##80023800,8#!##800237?8,8#!##800237?0,8#!##800237>8,8#!##800237>0,8#!##800237=8,8#!##800237=0,8#!##800237<8,8#!##800237<0,8#!##800237;8,8#!##800237;0,8#!##800237:8,8#!##800237:0,8#!##80023798,8#!##80023790,8#!##80023788,8#!##80023780,8#!##80023778,8#!##80023770,8#!##80023768,8#!##80023760,8#!##80023758,8#!##80023750,8#!##80023748,8#!##80023740,8#!##80023738,8#!##80023730,8#!##8002372<,4#!##80023728,4#!##80023724,4#!##80023720,4#!##8002371<,4#!##80023718,4#!##80023870,4#!##80023714,4#!$2-138,8^#2#!$2-130,8#15<3:0!$2-128,8#1=010!$2-120,8#2!$2-118,8#1!$2-110,8^#2#!$2-108,8#67?>0!##800222:<,4#!##800222:8,4#!##800222;0,4#!##800222:4,4#!##7???<>40,8#!##7???<>38,8#!##7???<>30,8#!##7???<>28,8#!##7???<>24,4#!##7???<>20,4#!##7???<>1<,4#!##7???<>4<,4#!##7???<>48,4#!##7???<>18,4#!##7???<>14,4#!##7???<>50,4#!##7???<>10,4#!##7???<>08,4#!##7???<>04,4#!##7???<>0<,4#!##7???<=?6,1#!##7???<=?5,1#!##7???<=?7,1#!##7???<=?4,1#!##7???<=?2,1#!##7???<=?1,1#!##7???<=?3,1#!##7???<=?0,1#!##7???<=>>,1#!##7???<=>=,1#!##7???<=>?,1#!##7???<=><,1#!##7???<=>:,1#!##7???<=>9,1#!##7???<=>;,1#!##7???<=>8,1#!##7???<=<2,1#!##7???<=<1,1#!##7???<=<3,1#!##7???<=<0,1#!##7???<=;8,4#!##7???<=;4,4#!##7???<=;<,4#!##7???<=:<,4#!##7???<=:8,4#!##7???<=;0,4#!##7???<=:0,4#!##7???<=9<,4#!##7???<=:4,4#!##7???<=94,4#!##7???<=90,4#!##7???<=98,4#!##7???<=88,4#!##7???<=84,4#!##7???<=8<,4#!##7???<=7<,4#!##7???<=78,4#!##7???<=80,4#!##7???<=74,1#!##7???<=73,1#!##7???<=76,1#!##7???<=75,1#!##7???<=72,1#!##7???<=71,1#!##7???<=77,1#!##7???<=70,1#!##7???<=6<,1#!##7???<=6;,1#!##7???<=6>,1#!##7???<=6=,1#!##7???<=6:,1#!##7???<=69,1#!##7???<=6?,1#!##7???<=68,1#!##7???<=60,4#!##7???<=5<,4#!##7???<=64,4#!##7???<=58,4#!##7???<=50,4#!##7???<=4<,4#!##7???<=54,4#!##7???<=44,4#!##7???<=40,4#!##7???<=48,4#!##7???<=38,4#!##7???<=34,4#!##7???<=3<,4#!##7???<=2<,4#!##7???<=28,4#!##7???<=30,4#!##7???<=20,4#!##7???<=1<,4#!##7???<=24,4#!##7???<=14,4#!##7???<=10,4#!##7???<=18,4#!##7???<=0>,1#!##7???<=0=,1#!##7???<=0?,1#!##7???<=0<,1#!##7???<=08,1#!##7???<=07,1#!##7???<=0:,1#!##7???<=09,1#!##7???<=06,1#!##7???<=05,1#!##7???<=0;,1#!##7???<=04,1#!##7???<=00,1#!##7???<<??,1#!##7???<=02,1#!##7???<=01,1#!##7???<<?>,1#!##7???<<?=,1#!##7???<=03,1#!##7???<<?<,1#!##7???<<<>,1#!##7???<<<=,1#!##7???<<<?,1#!##7???<<<<,1#!##7???<<;6,1#!##7???<<;5,1#!##7???<<;7,1#!##7???<<;4,1#!##7???<<;2,1#!##7???<<;1,1#!##7???<<;3,1#!##7???<<;0,1#!##7???<<:>,1#!##7???<<:=,1#!##7???<<:?,1#!##7???<<:<,1#!##7???<<::,1#!##7???<<:9,1#!##7???<<:;,1#!##7???<<:8,1#!##7???<<:6,1#!##7???<<:5,1#!##7???<<:7,1#!##7???<<:4,1#!##7???<<9<,4#!##7???<<98,4#!##7???<<:0,4#!##7???<<94,4#!##7???<<92,1#!##7???<<91,1#!##7???<<93,1#!##7???<<90,1#!##7???<<78,8#!##7???<<70,8#!##7???<<68,8#!##7???<<60,8#!##7???<<58,8#!##7???<<50,8#!##7???<<48,8#!##7???<<40,8#!##7???<<38,8#!##7???<<30,8#!##7???<<28,8#!##7???<<20,8#!##7???<<18,8#!##7???<<10,8#!##7???<<08,8#!##7???<<00,8#!##7???<;?8,8#!##7???<;?0,8#!##7???<;>8,8#!##7???<;>0,8#!##7???<;=8,8#!##7???<;=0,8#!##7???<;<8,8#!##7???<;<0,8#!##7???<;;8,8#!##7???<;;0,8#!##7???<;:8,8#!##7???<;:0,8#!##7???<;98,8#!##7???<;90,8#!##7???<;88,8#!##7???<;80,8#!##7???<;78,8#!##7???<;70,8#!##7???<;68,8#!##7???<;60,8#!##7???<;58,8#!##7???<;50,8#!##7???<;48,8#!##7???<;40,8#!##7???<;38,8#!##7???<;30,8#!##7???<;28,8#!##7???<;20,8#!##7???<;18,8#!##7???<;10,8#!##7???<;08,8#!##7???<;00,8#!##7???<<80,4#!##7???<:?<,4#!##7???<:?8,4#!##7???<:?4,4#!##7???<:?0,4#!##7???<<88,4#!##7???<<84,4#!##7???<:><,4#!##7???<:>8,4#!##7???<<8<,4#!##7???<:>4,4#!##7???<:<0,8#!##7???<:;8,8#!##7???<:;0,8#!##7???<::8,8#!##7???<::0,8#!##7???<:98,8#!##7???<:90,8#!##7???<:88,8#!##7???<:80,8#!##7???<:78,8#!##7???<:70,8#!##7???<:68,8#!##7???<:60,8#!##7???<:58,8#!##7???<:50,8#!##7???<:48,8#!##7???<:40,8#!##7???<:38,8#!##7???<:30,8#!##7???<:28,8#!##7???<:20,8#!##7???<:18,8#!##7???<:10,8#!##7???<:08,8#!##7???<:00,8#!##7???<9?8,8#!##7???<9?0,8#!##7???<9>8,8#!##7???<9>0,8#!##7???<9=8,8#!##7???<9=0,8#!##7???<9<8,8#!##7???<9<0,8#!##7???<9;8,8#!##7???<9;0,8#!##7???<9:8,8#!##7???<9:0,8#!##7???<998,8#!##7???<990,8#!##7???<988,8#!##7???<980,8#!##7???<978,8#!##7???<970,8#!##7???<968,8#!##7???<960,8#!##7???<958,8#!##7???<950,8#!##7???<948,8#!##7???<940,8#!##7???<938,8#!##7???<930,8#!##7???<928,8#!##7???<920,8#!##7???<918,8#!##7???<910,8#!##7???<908,8#!##7???<900,8#!##7???<8?8,8#!##7???<8?0,8#!##7???<8>8,8#!##7???<8>0,8#!##7???<8=8,8#!##7???<8=0,8#!##7???<8<8,8#!##7???<8<0,8#!##7???<8;8,8#!##7???<8;0,8#!##7???<8:8,8#!##7???<8:0,8#!##7???<898,8#!##7???<890,8#!##7???<888,8#!##7???<880,8#!##7???<878,8#!##7???<870,8#!##7???<868,8#!##7???<860,8#!##7???<858,8#!##7???<850,8#!##7???<848,8#!##7???<840,8#!##7???<838,8#!##7???<830,8#!##7???<828,8#!##7???<820,8#!##7???<818,8#!##7???<810,8#!##7???<808,8#!##7???<800,8#!##7???<7?8,8#!##7???<7?0,8#!##7???<7>8,8#!##7???<7>0,8#!##7???<7=8,8#!##7???<7=0,8#!##7???<7<8,8#!##7???<7<0,8#!##7???<7;8,8#!##7???<7;0,8#!##7???<7:8,8#!##7???<:=4,4#!##7???<:=0,4#!##7???<:<<,4#!##7???<:<8,4#!##7???<7:4,4#!##7???<7:0,4#!##7???<79<,4#!##7???<798,4#!##7???<:=<,4#!##7???<:=8,4#!##7???<794,4#!##7???<790,4#!##7???<:>0,4#!##7???<78<,4#!##7???<78:,1#!##7???<789,1#!##7???<78;,1#!##7???<788,1#!##7???<786,1#!##7???<785,1#!##7???<787,1#!##7???<784,1#!##7???<774,1#!##7???<773,1#!##7???<776,1#!##7???<775,1#!##7???<772,1#!##7???<771,1#!##7???<777,1#!##7???<770,1#!##7???<76>,1#!##7???<76=,1#!##7???<76?,1#!##7???<76<,1#!##7???<764,4#!##7???<760,4#!##7???<768,4#!##7???<75>,1#!##7???<75=,1#!##7???<75?,1#!##7???<75<,1#!##7???<750,4#!##7???<74<,4#!##7???<754,4#!##7???<74:,1#!##7???<749,1#!##7???<74;,1#!##7???<748,1#!$2-=0,8#1>?520!$2-=8,8#160760!$2-<8,8#160770!$2-<0,8#160768!$2->8,8#2<!$2-?0,8#15=2?0!$2-?8,8#15=338!$2->0,8#15;8:0!$2-;8,8$1;!$2-;0,8$1:!$2-:8,8$19!$2-:0,8$18!$2-98,8$17!$2-90,8$16!$2-88,8$15!$2-80,8$14!$2-78,8$13!$2-70,8$12!$2-68,8#1508?0!$2-60,8#15<3<0!$2-58,8#68274!$2-50,8#1508?0!$2-48,8#=5694!$2-38,8#137<:<!##15<410,1#1!$2-40,8#1508?0!##6;3;50,1#1!##6;3;60,8#!##6;3;58,4#20!##6;3=70,4$2<!$2-10,8$8!$2-8,8$1'$2#7???7?811000#800000000000&$2#10($2-140#140,$2-140#8,$2-100#8%#10000#158000(##15<3<0#8(##15<410#1(##15=330#8(##6;3;50#1(##6;3;58#4(##6;3;60#8(##6;3=70#4(##7???<748#1(##7???<749#1(##7???<74:#1(##7???<74;#1(##7???<74<#1(##7???<74<#4(##7???<74=#1(##7???<74>#1(##7???<74?#1(##7???<750#4(##7???<754#1(##7???<754#4(##7???<755#1(##7???<756#1(##7???<757#1(##7???<75<#1(##7???<75=#1(##7???<75>#1(##7???<75?#1(##7???<760#1(##7???<760#4(##7???<761#1(##7???<762#1(##7???<763#1(##7???<764#4(##7???<768#1(##7???<768#4(##7???<769#1(##7???<76:#1(##7???<76;#1(##7???<76<#1(##7???<76=#1(##7???<76>#1(##7???<76?#1(##7???<770#1(##7???<771#1(##7???<772#1(##7???<773#1(##7???<774#1(##7???<775#1(##7???<776#1(##7???<777#1(##7???<784#1(##7???<785#1(##7???<786#1(##7???<787#1(##7???<788#1(##7???<789#1(##7???<78:#1(##7???<78;#1(##7???<78<#1(##7???<78<#4(##7???<78=#1(##7???<78>#1(##7???<78?#1(##7???<790#4(##7???<794#4(##7???<798#4(##7???<79<#4(##7???<7:0#4(##7???<7:4#4(##7???<7:8#8(##7???<7;0#8(##7???<7;8#8(##7???<7<0#8(##7???<7<8#8(##7???<7=0#8(##7???<7=8#8(##7???<7>0#8(##7???<7>8#8(##7???<7?0#8(##7???<7?8#8(##7???<800#8(##7???<808#8(##7???<810#8(##7???<818#8(##7???<820#8(##7???<828#8(##7???<830#8(##7???<838#8(##7???<840#8(##7???<848#8(##7???<850#8(##7???<858#8(##7???<860#8(##7???<868#8(##7???<870#8(##7???<878#8(##7???<880#8(##7???<888#8(##7???<890#8(##7???<898#8(##7???<8:0#8(##7???<8:8#8(##7???<8;0#8(##7???<8;8#8(##7???<8<0#8(##7???<8<8#8(##7???<8=0#8(##7???<8=8#8(##7???<8>0#8(##7???<8>8#8(##7???<8?0#8(##7???<8?8#8(##7???<900#8(##7???<908#8(##7???<910#8(##7???<918#8(##7???<920#8(##7???<928#8(##7???<930#8(##7???<938#8(##7???<940#8(##7???<948#8(##7???<950#8(##7???<958#8(##7???<960#8(##7???<968#8(##7???<970#8(##7???<978#8(##7???<980#8(##7???<988#8(##7???<990#8(##7???<998#8(##7???<9:0#8(##7???<9:8#8(##7???<9;0#8(##7???<9;8#8(##7???<9<0#8(##7???<9<8#8(##7???<9=0#8(##7???<9=8#8(##7???<9>0#8(##7???<9>8#8(##7???<9?0#8(##7???<9?8#8(##7???<:00#8(##7???<:08#8(##7???<:10#8(##7???<:18#8(##7???<:20#8(##7???<:28#8(##7???<:30#8(##7???<:38#8(##7???<:40#8(##7???<:48#8(##7???<:50#8(##7???<:58#8(##7???<:60#8(##7???<:68#8(##7???<:70#8(##7???<:78#8(##7???<:80#8(##7???<:88#8(##7???<:90#8(##7???<:98#8(##7???<::0#8(##7???<::8#8(##7???<:;0#8(##7???<:;8#8(##7???<:<0#8(##7???<:<8#4(##7???<:<<#4(##7???<:=0#4(##7???<:=4#4(##7???<:=8#4(##7???<:=<#4(##7???<:>0#1(##7???<:>0#4(##7???<:>1#1(##7???<:>2#1(##7???<:>3#1(##7???<:>4#1(##7???<:>4#4(##7???<:>5#1(##7???<:>6#1(##7???<:>7#1(##7???<:>8#4(##7???<:><#4(##7???<:?0#4(##7???<:?4#4(##7???<:?8#4(##7???<:?<#4(##7???<;00#8(##7???<;08#8(##7???<;10#8(##7???<;18#8(##7???<;20#8(##7???<;28#8(##7???<;30#8(##7???<;38#8(##7???<;40#8(##7???<;48#8(##7???<;50#8(##7???<;58#8(##7???<;60#8(##7???<;68#8(##7???<;70#8(##7???<;78#8(##7???<;80#8(##7???<;88#8(##7???<;90#8(##7???<;98#8(##7???<;:0#8(##7???<;:8#8(##7???<;;0#8(##7???<;;8#8(##7???<;<0#8(##7???<;<8#8(##7???<;=0#8(##7???<;=8#8(##7???<;>0#8(##7???<;>8#8(##7???<;?0#8(##7???<;?8#8(##7???<<00#8(##7???<<08#8(##7???<<10#8(##7???<<18#8(##7???<<20#8(##7???<<28#8(##7???<<30#8(##7???<<38#8(##7???<<40#8(##7???<<48#8(##7???<<50#8(##7???<<58#8(##7???<<60#8(##7???<<68#8(##7???<<70#8(##7???<<74#4(##7???<<78#4(##7???<<78#8(##7???<<7<#4(##7???<<80#4(##7???<<84#4(##7???<<88#4(##7???<<8<#1(##7???<<8<#4(##7???<<8=#1(##7???<<8>#1(##7???<<8?#1(##7???<<90#1(##7???<<91#1(##7???<<92#1(##7???<<93#1(##7???<<94#1(##7???<<94#4(##7???<<95#1(##7???<<96#1(##7???<<97#1(##7???<<98#4(##7???<<9<#4(##7???<<:0#1(##7???<<:0#4(##7???<<:1#1(##7???<<:2#1(##7???<<:3#1(##7???<<:4#1(##7???<<:5#1(##7???<<:6#1(##7???<<:7#1(##7???<<:8#1(##7???<<:9#1(##7???<<::#1(##7???<<:;#1(##7???<<:<#1(##7???<<:=#1(##7???<<:>#1(##7???<<:?#1(##7???<<;0#1(##7???<<;1#1(##7???<<;2#1(##7???<<;3#1(##7???<<;4#1(##7???<<;5#1(##7???<<;6#1(##7???<<;7#1(##7???<<<<#1(##7???<<<=#1(##7???<<<>#1(##7???<<<?#1(##7???<<?<#1(##7???<<?=#1(##7???<<?>#1(##7???<<??#1(##7???<=00#1(##7???<=01#1(##7???<=02#1(##7???<=03#1(##7???<=04#1(##7???<=05#1(##7???<=06#1(##7???<=07#1(##7???<=08#1(##7???<=09#1(##7???<=0:#1(##7???<=0;#1(##7???<=0<#1(##7???<=0=#1(##7???<=0>#1(##7???<=0?#1(##7???<=10#1(##7???<=10#4(##7???<=11#1(##7???<=12#1(##7???<=13#1(##7???<=14#4(##7???<=18#1(##7???<=18#4(##7???<=19#1(##7???<=1:#1(##7???<=1;#1(##7???<=1<#1(##7???<=1<#4(##7???<=1=#1(##7???<=1>#1(##7???<=1?#1(##7???<=20#4(##7???<=24#1(##7???<=24#4(##7???<=25#1(##7???<=26#1(##7???<=27#1(##7???<=28#1(##7???<=28#4(##7???<=29#1(##7???<=2:#1(##7???<=2;#1(##7???<=2<#4(##7???<=30#1(##7???<=30#4(##7???<=31#1(##7???<=32#1(##7???<=33#1(##7???<=34#1(##7???<=34#4(##7???<=35#1(##7???<=36#1(##7???<=37#1(##7???<=38#4(##7???<=3<#1(##7???<=3<#4(##7???<=3=#1(##7???<=3>#1(##7???<=3?#1(##7???<=40#1(##7???<=40#4(##7???<=41#1(##7???<=42#1(##7???<=43#1(##7???<=44#4(##7???<=48#1(##7???<=48#4(##7???<=49#1(##7???<=4:#1(##7???<=4;#1(##7???<=4<#1(##7???<=4<#4(##7???<=4=#1(##7???<=4>#1(##7???<=4?#1(##7???<=50#4(##7???<=54#1(##7???<=54#4(##7???<=55#1(##7???<=56#1(##7???<=57#1(##7???<=58#1(##7???<=58#4(##7???<=59#1(##7???<=5:#1(##7???<=5;#1(##7???<=5<#4(##7???<=60#4(##7???<=64#1(##7???<=64#4(##7???<=65#1(##7???<=66#1(##7???<=67#1(##7???<=68#1(##7???<=69#1(##7???<=6:#1(##7???<=6;#1(##7???<=6<#1(##7???<=6=#1(##7???<=6>#1(##7???<=6?#1(##7???<=70#1(##7???<=71#1(##7???<=72#1(##7???<=73#1(##7???<=74#1(##7???<=75#1(##7???<=76#1(##7???<=77#1(##7???<=78#1(##7???<=78#4(##7???<=79#1(##7???<=7:#1(##7???<=7;#1(##7???<=7<#4(##7???<=80#1(##7???<=80#4(##7???<=81#1(##7???<=82#1(##7???<=83#1(##7???<=84#1(##7???<=84#4(##7???<=85#1(##7???<=86#1(##7???<=87#1(##7???<=88#4(##7???<=8<#1(##7???<=8<#4(##7???<=8=#1(##7???<=8>#1(##7???<=8?#1(##7???<=90#1(##7???<=90#4(##7???<=91#1(##7???<=92#1(##7???<=93#1(##7???<=94#4(##7???<=98#1(##7???<=98#4(##7???<=99#1(##7???<=9:#1(##7???<=9;#1(##7???<=9<#1(##7???<=9<#4(##7???<=9=#1(##7???<=9>#1(##7???<=9?#1(##7???<=:0#4(##7???<=:4#1(##7???<=:4#4(##7???<=:5#1(##7???<=:6#1(##7???<=:7#1(##7???<=:8#1(##7???<=:8#4(##7???<=:9#1(##7???<=::#1(##7???<=:;#1(##7???<=:<#4(##7???<=;0#1(##7???<=;0#4(##7???<=;1#1(##7???<=;2#1(##7???<=;3#1(##7???<=;4#1(##7???<=;4#4(##7???<=;5#1(##7???<=;6#1(##7???<=;7#1(##7???<=;8#4(##7???<=;<#1(##7???<=;<#4(##7???<=;=#1(##7???<=;>#1(##7???<=;?#1(##7???<=<0#1(##7???<=<1#1(##7???<=<2#1(##7???<=<3#1(##7???<=>8#1(##7???<=>9#1(##7???<=>:#1(##7???<=>;#1(##7???<=><#1(##7???<=>=#1(##7???<=>>#1(##7???<=>?#1(##7???<=?0#1(##7???<=?1#1(##7???<=?2#1(##7???<=?3#1(##7???<=?4#1(##7???<=?5#1(##7???<=?6#1(##7???<=?7#1(##7???<>04#1(##7???<>04#4(##7???<>05#1(##7???<>06#1(##7???<>07#1(##7???<>08#4(##7???<>0<#1(##7???<>0<#4(##7???<>0=#1(##7???<>0>#1(##7???<>0?#1(##7???<>10#1(##7???<>10#4(##7???<>11#1(##7???<>12#1(##7???<>13#1(##7???<>14#4(##7???<>18#4(##7???<>1<#4(##7???<>20#4(##7???<>24#4(##7???<>28#4(##7???<>28#8(##7???<>30#8(##7???<>38#4(##7???<>38#8(##7???<>3<#4(##7???<>40#4(##7???<>40#8(##7???<>44#4(##7???<>48#4(##7???<>4<#4(##7???<>50#1(##7???<>50#4(##7???<>51#1(##7???<>52#1(##7???<>53#1(##800222:4#1(##800222:4#4(##800222:5#1(##800222:6#1(##800222:7#1(##800222:8#4(##800222:<#4(##800222;0#1(##800222;0#4(##800222;1#1(##800222;2#1(##800222;3#1(##80023714#1(##80023714#4(##80023715#1(##80023716#1(##80023717#1(##80023718#4(##8002371<#4(##80023720#4(##80023724#4(##80023728#4(##8002372<#4(##80023730#8(##80023738#8(##80023740#8(##80023748#8(##80023750#8(##80023758#8(##80023760#8(##80023768#8(##80023770#8(##80023778#8(##80023780#8(##80023788#8(##80023790#8(##80023798#8(##800237:0#8(##800237:8#8(##800237;0#8(##800237;8#8(##800237<0#8(##800237<8#8(##800237=0#8(##800237=8#8(##800237>0#8(##800237>8#8(##800237?0#8(##800237?8#8(##80023800#8(##80023808#8(##80023810#8(##80023818#8(##80023820#8(##80023828#8(##80023830#8(##80023838#8(##80023840#8(##80023848#8(##80023850#8(##80023858#8(##80023858#4(##8002385<#4(##80023860#8(##80023860#4(##80023864#4(##80023868#8(##80023868#4(##8002386<#4(##80023870#1(##80023870#4(##80023871#1(##80023872#1(##80023873#1!##693:58,4$2<'$2<#1#3?????!##6;3=93,1#!##6;3;70,8#137<74!##6;3<70,8#9>48<!##6;3;54,4#!##1?1920,1#!##6;3;68,8#!##158;:8,8#158;:8!##15=290,4#1!##160758,1#1!##15?:78,8#7???8000!##15;8:0,8#23:40!##15;8;0,1#20!##15?2=<,1#1!##15;8;0,8#20!##1?1620,8^#?#???????????????!##158=:8,8#14916<!##15;8=8,8^#?#???????????????!##15;8>0,8#23:60!##15;8?0,1#60!##15;8?0,8#60!##15;918,8^#?#???????????????!##15;920,8#23:>0!##15;930,1#20!##15;930,8#20!##15;958,8^#?#???????????????!##15;960,8#23;00!##15;970,1#60!##15;970,8#60!##15;998,8^#?#???????????????!##15;9:0,8#23;60!##15;9;0,1#20!##15;9;0,8#20!##15;9=8,8^#?#???????????????!##15;9>0,8#23;80!##15;9?0,1#40!##15;9?0,8#40!##15;:18,8^#?#???????????????!##15;:20,8#23<20!##15;:30,1#20!##15;:30,8#20!##15;:58,8^#?#???????????????!##15;:60,8#23<40!##15;:70,1#20!##15;:70,8#20!##15;:98,8^#?#???????????????!##15;::0,8#23<60!##15;:;0,1#<0!##15;:;0,8#1:<0!##15;:=8,8^#?#???????????????!##15;:>0,8#25720!##15;:?0,1#60!##15;:?0,8#=60!##15;;18,8^#?#???????????????!##15;;20,8#26480!##15;;30,1#20!##15;;30,8#20!##15;;58,8^#?#???????????????!##15;;60,8#264:0!##15;;70,1#80!##15;;70,8#80!##15;;98,8^#?#???????????????!##15;;:0,8#26520!##15;;;0,1#20!##15;;;0,8#20!##15;;=8,8^#?#???????????????!##15;;>0,8#26540!##15;;?0,1#20!##15;;?0,8#20!##15;<18,8^#?#???????????????!##15;<20,8#26560!##15;<30,1#20!##15;<30,8#20!##15;<58,8^#?#???????????????!##15;<60,8#26580!##15;<70,1#20!##15;<70,8#20!##15;<98,8^#?#???????????????!##15;<:0,8#265:0!##15;<;0,1#20!##15;<;0,8#20!##15;<=8,8^#?#???????????????!##15;<>0,8#26660!##15;<?0,1#20!##15;<?0,8#20!##15;=18,8^#?#???????????????!##15;=20,8#267>0!##15;=30,1#40!##15;=30,8#40!##15;=58,8^#?#???????????????!##15;=60,8#26820!##15;=70,1#40!##15;=70,8#40!##15;=98,8^#?#???????????????!##15;=:0,8#26860!##15;=;0,1#20!##15;=;0,8#20!##15;==8,8^#?#???????????????!##15;=>0,8#26880!##15;=?0,1#60!##15;=?0,8#60!##15;>18,8^#?#???????????????!##15;>20,8#268>0!##15;>30,1#60!##15;>30,8#60!##15;>58,8^#?#???????????????!##15;>60,8#26940!##15;>70,1#60!##15;>70,8#60!##15;>98,8^#?#???????????????!##15;>:0,8#269:0!##15;>;0,1#60!##15;>;0,8#60!##15;>=8,8^#?#???????????????!##15;>>0,8#26:00!##15;>?0,1#60!##15;>?0,8#60!##15;?18,8^#?#???????????????!##15;?20,8#26:60!##15;?30,1#60!##15;?30,8#60!##15;?58,8^#?#???????????????!##15;?60,8#26:<0!##15;?70,1#80!##15;?70,8#80!##15;?98,8^#?#???????????????!##15;?:0,8#26;40!##15;?;0,1#40!##15;?;0,8#40!##15;?=8,8^#?#???????????????!##15;?>0,8#26;80!##15;??0,1#40!##15;??0,8#40!##15<018,8^#?#???????????????!##15<020,8#26;<0!##15<030,1#60!##15<030,8#60!##15<058,8^#?#???????????????!##15<060,8#26<20!##15<070,1#60!##15<070,8#60!##15<098,8^#?#???????????????!##15<0:0,8#26<80!##15<0;0,1#60!##15<0;0,8#60!##15<0=8,8^#?#???????????????!##15<0>0,8#26<>0!##15<0?0,1#60!##15<0?0,8#60!##15<118,8^#?#???????????????!##15<120,8#26=40!##15<130,1#60!##15<130,8#60!##15<158,8^#?#???????????????!##15<160,8#26=:0!##15<170,1#60!##15<170,8#60!##15<198,8^#?#???????????????!##15<1:0,8#26>00!##15<1;0,1#20!##15<1;0,8#20!##15<1=8,8^#?#???????????????!##15<1>0,8#26?40!##15<1?0,1#20!##15<1?0,8#20!##15<218,8^#?#???????????????!##15<220,8#26?60!##15<230,1#20!##15<230,8#20!##15<258,8^#?#???????????????!##15<260,8#26?80!##15<270,1#20!##15<270,8#20!##15<298,8^#?#???????????????!##15<2:0,8#26?:0!##15<2;0,1#20!##15<2;0,8#20!##15<2=8,8^#?#???????????????!##15<2>0,8#27020!##15<2?0,1#60!##15<2?0,8#60!##15<318,8^#?#???????????????!##15<320,8#27080!##15<330,1#20!##15<330,8#220!##15<358,8^#?#???????????????!##15<360,8#151520!##15<370,1#80!##15<370,8#80!##15<398,8^#?#???????????????!##6;4308,8#!##15;868,8#15;780!##15;80<,4#????????!##15;7:8,8#!##15;7;8,8#!##15;788,8#!##15;790,8#!##15;778,8#15;690!##15;71<,4#????????!##15;6;8,8#!##15;6<8,8#!##15;698,8#!##15;6:0,8#!##15;688,8#15;5:0!##15;62<,4#????????!##15;5<8,8#6;4318!##15;5=8,8#6;4318!##15;5:8,8#!##15;5;0,8#,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1276376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_572cde.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1277128 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_572cde.IT BndT_Na_001.SegItab_Na_572cde.IT_sound BF NX0 BR XSTEP F0 PSS plan 1277128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_dpXm.

Module LibSegNa_drA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_fff2e7.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_fff2e7.IT.
Definition ENDS : list Z := [451544].
Definition STOPS1 : list Z := [451544] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 715920; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 1422752; ELit 129235; (EVar 33); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-930#930,$2-930#930%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-930#930$21#+$22#1!##7???;?18,8#!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000"%pstring).
Definition ss0 : sym_state := SS 434916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2352), ELit 2352)].
Definition F0L : list SR.region := [(EVar 2, (-2352), 2352)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6>3=8#6>3=8#5=#6>3=8,20##6>2=0+$2-930$3$4$5$6$7+$2-70^#?#???????????????$21##73#73#$?$10$11#:#1?8>8#15?1>+$2-28$21#9+$2-8?8^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?,,3=!$2-8?4,1#73!$2-900,8#1?8>8!$2-8?8,1#!$2-908,8#1?8>6!$2-910,8^#?#???????????????!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-911,1#!$2-912,1#!$2-913,1#!$2-914,1#!$2-915,1#!$2-916,1#!$2-917,1#!$2-918,1#!$2-928,8+$2->8!$2-920,8#2105>!$2-=8,8$1;!$2-=0,8$1:!$2-<8,8$19!$2-<0,8$18!$2-;8,8$17!$2-;0,8$16!$2-:8,8$15!$2-:0,8$14!$2-98,8$13!$2-90,8+$2-30!$2-88,8#15;5:0!$2-80,8#1?8=3!$2-78,8#6?258!$2-60,8+$2-30!$2-58,8+$2-30!$2-68,8+$2-30!$2-18,8$?!$2-20,8$>!$2-28,8$=!$2-30,8$21!$2-8,8$11!$2-10,8$10!$2-50,8$12!$2-48,8$9!$2-40,8$8!$2-38,8#:><90'$2#7???7?811000#800000000000&$2#10($2-930#930,$2-930#8,$2-8?0#818,$2-70#8%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-930#930$21#+$22#1!##7???;?18,8#!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 451544 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_fff2e7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 434916 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_fff2e7.IT BndT_Na_003.SegItab_Na_fff2e7.IT_sound BF NX0 BR XSTEP F0 PSS plan 434916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drA.

Module LibSegNa_drB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_5bdf21.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_5bdf21.IT.
Definition ENDS : list Z := [434840].
Definition STOPS1 : list Z := [434840] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7+$2#8<0$9$:$;$<$=$>$?$10$11$12#1?8>8$78$79$7:$7;+$2#38^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#<40%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#20!##7???;?18,8#(##15;5:0#4(##15;5:8#8(##15;5;0#8(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8(##15;628#4!$2#8;8,8#6?258!$2#8;0,8#1?8=3!$2#8:8,8#15;5:0!$2#8:0,8+$2#900!$2#898,8$13!$2#890,8$14!$2#888,8$15!$2#880,8$16!$2#878,8$17!$2#870,8$18!$2#868,8$19!$2#860,8$1:!$2#858,8$1;!##158<28,8#14056<!$2#8=8,8+$2#900!##6;3;40,8$28!##15;62<,4#????????!##15;5:0,4#5!##15;600,8#!##15;5?8,8#6;4318!##15;628,4#!##15;630,4#????????!##160759,1#1!##15?:78,8#7???8000!##158=:0,8#148=68!$2#900,8$21"%pstring).
Definition ss0 : sym_state := SS 451388 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-896), ELit 3136); (ELit 0, (1422752), ELit 4); (ELit 0, (1422760), ELit 8); (ELit 0, (1422768), ELit 8); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8); (ELit 0, (1422840), ELit 8); (ELit 0, (1422848), ELit 8); (ELit 0, (1422888), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-896), 3136); (ELit 0, (1422752), 4); (ELit 0, (1422760), 8); (ELit 0, (1422768), 8); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8); (ELit 0, (1422840), 8); (ELit 0, (1422848), 8); (ELit 0, (1422888), 4)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6:298#6:298#5=#6:298,20##140=34+$2#530$3$4##72#20#25#7???????$21#7???????+$2#750+$2#908#1?^#?#?????????????<6#73#8#7?????><#13#15;5:0#1?8>8#$21#^#?#???????????????###6?$1=$1>$1?,,96!$2#5:0,8$21!$2#750,8+$2#908!##15;5<8,8+$2#773!$2#4:0,8$18!$2#4:8,8#1?8>6!$2#4;0,8#!$2#4;8,8#1?8>6!$2#4<0,8#15;5:0!$2#4<8,8#!$2#4=0,8#1?8>6!$2#4=8,8#!$2#4>0,8#15;5:0!$2#4>8,8#140120!$2#4?8,8#1?8>6!$2#500,8#15;5:0!$2#508,8#13!$2#510,8#7?????><!$2#518,8#7???????!$2#520,8#25!$2#528,8#140864!$2#772,1#20!$2#771,1#6>!$2#770,1#6?!$2#76?,1#20!$2#76>,1#72!$2#76=,1#6?!$2#76<,1#72!$2#76;,1#72!$2#76:,1#65!$2#769,1#20!$2#768,1#64!$2#767,1#61!$2#766,1#65!$2#765,1#72!$2#764,1#20!$2#763,1#3:!$2#762,1#69!$2#761,1#6<!$2#760,1#63!$2#558,8^#?#???????<<<<<<<=!$2#560,8^#?#??????????>????!$2#598,8#<<<<<<<!$2#580,8#12889!$2#6>0,8$28!$2#590,8#6;3;40!$2#588,8#!$2#578,8+$2#750!$2#568,8+$2#7;0!$2#570,8+$2#858!$2#6>8,8$1;!$2#6?0,8$1:!$2#6?8,8$19!$2#700,8$18!$2#708,8$17!$2#710,8$16!$2#718,8#5!$2#720,8#6;4318!$2#728,8#1!$2#730,8#6;3;40!$2#738,8#1?8=3!$2#740,8#15;5:0!$2#748,8#140674!##15;5<0,8+$2#7;0!##15;5;0,8#!##15;5:8,8#!##15;5=8,8+$2#760!##15;628,4^#?#???????????????!##15;600,8#50!##15;5?8,8+$2#760!##15;5:0,4#5!$2#870,8#!$2#868,8#!$2#860,8#!$2#858,8#!$2#878,8#!$2#758,8+$2#900!$2#880,8$28!$2#888,8$15!$2#890,8$14!$2#898,8$13!$2#8:0,8+$2#900!$2#8:8,8#15;5:0!$2#8;0,8#1?8=3!$2#8;8,8#6?298!$2#20,8^#?#???????????????!$2#3?,1#!$2#3>,1#!$2#3=,1#!$2#3<,1#!$2#3;,1#!$2#3:,1#!$2#39,1#!$2#38,1#!$2#37,1#!$2#36,1#!$2#35,1#!$2#34,1#!$2#33,1#!$2#32,1#!$2#31,1#!$2#30,1#!$2#2?,1#!$2#2>,1#!$2#2=,1#!$2#2<,1#!$2#2;,1#!$2#2:,1#!$2#29,1#!$2#28,1#!$2#1?,1#!$2#1>,1#!$2#1=,1#!$2#1<,1#!$2#1;,1#!$2#1:,1#!$2#19,1#!$2#18,1#'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#398,$2#40#460,$2#4?0#8,$2#530#28,$2#5:8#138,$2#773#>5%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#20!##7???;?18,8#(##15;5:0#4(##15;5:8#8(##15;5;0#8(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8(##15;628#4!##158<28,8#14056<!$2#8=8,8+$2#900!##6;3;40,8$28!##15;62<,4#????????!##15;630,4#????????!##160759,1#1!##15?:78,8#7???8000!##158=:0,8#148=68!$2#900,8$21,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 434840 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_5bdf21.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 451388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_5bdf21.IT BndT_Na_001.SegItab_Na_5bdf21.IT_sound BF NX0 BR XSTEP F0 PSS plan 451388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drB.

Module LibSegNa_drD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0a8470.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0a8470.IT.
Definition ENDS : list Z := [1315456].
Definition STOPS1 : list Z := [1315456] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????#1$;$<$=$>$?$10$11#7?????><#13#15;5:0#1?8>8#$21$18^#?#???????????????#$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#8>0%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-8;0#8>0$21#+$22#1(##15;5<8#8!##15;5:0,1#5!##15;5<0,8+$2#280!##15;5<8,8+$2#243!##15;630,4#????????!##160759,1#1!##158=:0,8#148=68!$21#1,1#"%pstring).
Definition ss0 : sym_state := SS 1314100 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2224), ELit 2272); (ELit 0, (1422792), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-2224), 2272); (ELit 0, (1422792), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#141280#141280#5=#141280,20##14115<$2$3$4$5$6$7#25#7???????$21#1#15;5:0+$2#243##3$10$11##13#15;5:0#1?8>8#$21##1#1#1$1<$1=$1>$1?,,28!##15;5<8,8+$2#243!$2-90,8#!$2-88,8$21!$2-80,8#!$2-78,8#1?8>8!$2-70,8#15;5:0!$2-68,8#!$2-60,8#10>4?!$2-58,8#!$2-50,8#15;5:0!$2-48,8#140120!$2-38,8#1?8>8!$2-30,8#15;5:0!$2-28,8#13!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#14115<!$2#8,8#!$2#20,8#1!$2#10,8#1!$2#,8#10>4?!$2#18,8#'$2#7???7?811000#800000000000&$2#10($2-8;0#8>0,$2-8;0#820,$2-40#8,$2#28#8%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-8;0#8>0$21#+$22#1(##15;5<8#8!##15;5:0,1#5!##15;5<0,8+$2#280!##15;630,4#????????!##160759,1#1!##158=:0,8#148=68!$21#1,1#,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1315456 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0a8470.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1314100 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0a8470.IT BndT_Na_000.SegItab_Na_0a8470.IT_sound BF NX0 BR XSTEP F0 PSS plan 1314100 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drD.

Module LibSegNa_drDs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_c5da15.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_c5da15.IT.
Definition ENDS : list Z := [519096].
Definition STOPS1 : list Z := [519096] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7#25#7???????$21#1#15;5:0$=$>$?$10$11##13#15;5:0#1?8>8$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#40%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-40#40$21#+$22#1!##15;5<0,8+$2#280!##15;5<8,8+$2#243!##15;630,4#????????"%pstring).
Definition ss0 : sym_state := SS 1315456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-64), ELit 64)].
Definition F0L : list SR.region := [(EVar 2, (-64), 64)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;8#7>;;8#5=#7>;;8,20##140120+$2-40$3$4$5$6$7#15;5:0#1+$2#243$21#1$=$>$?$10$11$21##15;5:0#1?8>8$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-38,8#1?8>8!$2-30,8#15;5:0!$2-28,8#13!$2-20,8#!$2-18,8#7???????!$2-10,8#25!$2-8,8#141284'$2#7???7?811000#800000000000&$2#10($2-40#40,$2-40#8%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-40#40$21#+$22#1!##15;5<0,8+$2#280!##15;5<8,8+$2#243!##15;630,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 519096 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_c5da15.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1315456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_c5da15.IT BndT_Na_002.SegItab_Na_c5da15.IT_sound BF NX0 BR XSTEP F0 PSS plan 1315456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drDs.

Module LibSegNa_drEa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_c5da15.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_c5da15.IT.
Definition ENDS : list Z := [519096].
Definition STOPS1 : list Z := [519096] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1422752; ELit 1; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; ELit 1; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#50%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-10#50$21#+$22#1(##15;5<8#8!##15;5<8,8+$2#283!$2#38,8#141284!$2#30,8#25!$2#28,8#7???????!$2#20,8#!$2#18,8#13!$2#10,8#15;5:0!$2#8,8#1?8>8!##15;5:0,1#5!##15;5<0,8+$2#2<0!##15;630,4#????????"%pstring).
Definition ss0 : sym_state := SS 1311008 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 80); (ELit 0, (1422792), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 80); (ELit 0, (1422792), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;8#7>;;8#5=#7>;;8,20##140120$2$3$4$5$6$7#15;5:0#1+$2#284#1?8>8#1$=$>$?$10$11#1?8>8##15;5:0#1?8>9#1#1?8>8$18$19#1$1;$1<$1=$1>$1?,,14!$2#8,8#1?8>9!$2#10,8#15;5:0!$2#18,8#14!$2#20,8#7?????>;!$2#28,8#7???????!$2#30,8#25!$2#38,8#140864!##15;5<8,8+$2#284'$2#7???7?811000#800000000000&$2#10($2-10#50,$2-10#18%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-10#50$21#+$22#1(##15;5<8#8!##15;5:0,1#5!##15;5<0,8+$2#2<0!##15;630,4#????????,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 519096 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_c5da15.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1311008 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_c5da15.IT BndT_Na_002.SegItab_Na_c5da15.IT_sound BF NX0 BR XSTEP F0 PSS plan 1311008 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drEa.

Module LibSegNa_drFa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_959642.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_959642.IT.
Definition ENDS : list Z := [1308256].
Definition STOPS1 : list Z := [1308256] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 1422752; ELit 1; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; ELit 0; EVar 20; EVar 21; ELit 1; EVar 123; EVar 124; EVar 125; ELit 1; EVar 127; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#270%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-10#270$21#+$22#1(##15;5<8#8!##15;5<8,8+$2#284!$2#38,8#140864!$2#30,8#25!$2#28,8#7???????!$2#20,8#7?????>;!$2#18,8#14!$2#10,8#15;5:0!$2#8,8#1?8>9!$2#:0,8#6;3;40!##6;3;40,8$28!$2#1?0,8$28!$2#258,8#140674!$2#250,8#15;5:0!$2#248,8#1?8=3!$2#240,8#6;3;40!$2#238,8#1!$2#230,8#6;4318!$2#228,8#5!$2#220,8$16!$2#218,8$17!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##15;5>8,8#13?624"%pstring).
Definition ss0 : sym_state := SS 1311008 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 624); (ELit 0, (1422792), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 624); (ELit 0, (1422792), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#13?660#13?660#5=#13?660,20##140694+$2#1?0$3$4$5$6$7##15;5:0$28###13?624$>$?$10$11#6;3;40#1#6;4318#6;3;40$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$2#218,8$28!$2#220,8$16!$2#228,8#!$2#230,8#6;4318!$2#238,8#1!$2#240,8#6;3;40!$2#248,8#15!$2#250,8#15;5:0!$2#258,8#140694!##15;5<8,8+$2#285'$2#7???7?811000#800000000000&$2#10($2-10#270,$2-10#228%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-10#270$21#+$22#1(##15;5<8#8!$2#38,8#140864!$2#30,8#25!$2#28,8#7???????!$2#20,8#7?????>;!$2#18,8#14!$2#10,8#15;5:0!$2#8,8#1?8>9!$2#:0,8#6;3;40!##6;3;40,8$28!$2#1?0,8$28!$2#210,8$18!$2#208,8$19!$2#200,8$1:!$2#1?8,8$1;!##15;5>8,8#13?624,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1308256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_959642.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1311008 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_959642.IT BndT_Na_002.SegItab_Na_959642.IT_sound BF NX0 BR XSTEP F0 PSS plan 1311008 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drFa.

Module LibSegNa_drGa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_81a787.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_81a787.IT.
Definition ENDS : list Z := [1277128].
Definition STOPS1 : list Z := [1277128] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; ELit 0; ELit 1422752; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 118; EVar 119; EVar 120; ELit 7027520; EVar 122; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##15;5?8,8+$2#80!##15;600,8#50!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8#15!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!##15;5:0,4#5!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8=3!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12"%pstring).
Definition ss0 : sym_state := SS 1308344 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-16), ELit 16); (ELit 0, (1422752), ELit 4); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8); (ELit 0, (1422840), ELit 8); (ELit 0, (1422848), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-16), 16); (ELit 0, (1422752), 4); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8); (ELit 0, (1422840), 8); (ELit 0, (1422848), 8)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#137<<8#137<<8#5=#137<<8,20##:><;<+$2#250$3$4$5$6$7$8$9#2$28$28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!##15;5:0,4#5!##15;600,8#!##15;5?8,8#6;4318!##15;5=8,8#!##15;5<8,8#!##15;5<0,8#'$2#7???7?811000#800000000000&$2#10($2-10#10,$2-10#10%#10000#158000'$21#7???7?811000#7?????????>?'$22#1#1)$2-10#10$21#+$22#1(##15;5:0#4(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8!##6;3;40,8$28!$2#28,8$28!$2#68,8#140694!$2#60,8#15;5:0!$2#58,8#15!$2#50,8#6;3;40!$2#48,8#1!$2#40,8#6;4318!$2#38,8#!$2#30,8$16!$2#1:0,8$28!$2#1=8,8#6?298!$2#1=0,8#1?8=3!$2#1<8,8#15;5:0!$2#1<0,8+$2#220!$2#1;8,8$13!$2#1;0,8$14!$2#1:8,8$15!$2#218,8#:><90!$2#210,8$8!$2#208,8$9!$2#200,8$12,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1277128 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_81a787.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1308344 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_81a787.IT BndT_Na_001.SegItab_Na_81a787.IT_sound BF NX0 BR XSTEP F0 PSS plan 1308344 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_drGa.

Module LibSegNa_duA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_fff2e7.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_fff2e7.IT.
Definition ENDS : list Z := [451544].
Definition STOPS1 : list Z := [451544] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 715744; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 1422752; ELit 91345; (EVar 33); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?811000#800000000000&$2#10($2-930#930,$2-930#930%#10000#158000'$21#7???7?811000#7?????????>?'$22##1????)$2-930#930$21#+$22#1!##7???:<98,8#!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000"%pstring).
Definition ss0 : sym_state := SS 434916 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-2352), ELit 2352)].
Definition F0L : list SR.region := [(EVar 2, (-2352), 2352)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6>3=8#6>3=8#5=#6>3=8,20##6>2=0+$2-930$3$4$5$6$7+$2-70^#?#???????????????$21##73#73#$?$10$11#:#164=:#15?1>+$2-28$21#9+$2-8?8^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?,,3=!$2-8?4,1#73!$2-900,8#164=:!$2-8?8,1#!$2-908,8#164=8!$2-910,8^#?#???????????????!$2-8?1,1#!$2-8?2,1#!$2-8?3,1#!$2-8?5,1#!$2-8?6,1#!$2-8?7,1#!$2-911,1#!$2-912,1#!$2-913,1#!$2-914,1#!$2-915,1#!$2-916,1#!$2-917,1#!$2-918,1#!$2-928,8+$2->8!$2-920,8#2105>!$2-=8,8$1;!$2-=0,8$1:!$2-<8,8$19!$2-<0,8$18!$2-;8,8$17!$2-;0,8$16!$2-:8,8$15!$2-:0,8$14!$2-98,8$13!$2-90,8+$2-30!$2-88,8#15;5:0!$2-80,8#164=1!$2-78,8#6?258!$2-60,8+$2-30!$2-58,8+$2-30!$2-68,8+$2-30!$2-18,8$?!$2-20,8$>!$2-28,8$=!$2-30,8$21!$2-8,8$11!$2-10,8$10!$2-50,8$12!$2-48,8$9!$2-40,8$8!$2-38,8#:>;>0'$2#7???7?811000#800000000000&$2#10($2-930#930,$2-930#8,$2-8?0#818,$2-70#8%#10000#158000'$21#7???7?811000#7?????????>?'$22##1????)$2-930#930$21#+$22#1!##7???:<98,8#!##160758,1#1!##1?15?<,1#1!##15?:78,8#7???8000,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 451544 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_fff2e7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 434916 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_fff2e7.IT BndT_Na_003.SegItab_Na_fff2e7.IT_sound BF NX0 BR XSTEP F0 PSS plan 434916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_duA.

Module LibSegNa_duB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_5bdf21.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_5bdf21.IT.
Definition ENDS : list Z := [434840].
Definition STOPS1 : list Z := [434840] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7+$2#8<0$9$:$;$<$=$>$?$10$11$12#164=:$78$79$7:$7;+$2#38^#:#:::::::::::::::^#?#???????????????#25$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2='$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#<40%#10000#158000'$21#7???7?811000#7?????????>?'$22##1????)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#18!##7???:<98,8#(##15;5:0#4(##15;5:8#8(##15;5;0#8(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8(##15;628#4!$2#8;8,8#6?258!$2#8;0,8#164=1!$2#8:8,8#15;5:0!$2#8:0,8+$2#900!$2#898,8$13!$2#890,8$14!$2#888,8$15!$2#880,8$16!$2#878,8$17!$2#870,8$18!$2#868,8$19!$2#860,8$1:!$2#858,8$1;!##158<28,8#14056<!$2#8=8,8+$2#900!##6;3;40,8$28!##15;62<,4#????????!##15;5:0,4#5!##15;600,8#!##15;5?8,8#6;4318!##15;628,4#!##15;630,4#????????!##160759,1#1!##15?:78,8#7???8000!##158=:0,8#148=68!$2#900,8$21"%pstring).
Definition ss0 : sym_state := SS 451388 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-896), ELit 3136); (ELit 0, (1422752), ELit 4); (ELit 0, (1422760), ELit 8); (ELit 0, (1422768), ELit 8); (ELit 0, (1422784), ELit 8); (ELit 0, (1422792), ELit 8); (ELit 0, (1422808), ELit 8); (ELit 0, (1422840), ELit 8); (ELit 0, (1422848), ELit 8); (ELit 0, (1422888), ELit 4)].
Definition F0L : list SR.region := [(EVar 2, (-896), 3136); (ELit 0, (1422752), 4); (ELit 0, (1422760), 8); (ELit 0, (1422768), 8); (ELit 0, (1422784), 8); (ELit 0, (1422792), 8); (ELit 0, (1422808), 8); (ELit 0, (1422840), 8); (ELit 0, (1422848), 8); (ELit 0, (1422888), 4)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6:298#6:298#5=#6:298,20##140=34+$2#530$3$4#$6$7#25#7???????$21#7???????+$2#750+$2#908#1?^#?#?????????????<6#73#8#7??????8#7#15;5:0#164=:#$21#^#?#???????????????##$1<$1=$1>$1?,,8:!$2#5:0,8$21!$2#750,8+$2#908!##15;5<8,8+$2#767!$2#4:0,8$18!$2#4:8,8#164=8!$2#4;0,8#!$2#4;8,8#164=8!$2#4<0,8#15;5:0!$2#4<8,8#!$2#4=0,8#164=8!$2#4=8,8#!$2#4>0,8#15;5:0!$2#4>8,8#140120!$2#4?8,8#164=8!$2#500,8#15;5:0!$2#508,8#7!$2#510,8#7??????8!$2#518,8#7???????!$2#520,8#25!$2#528,8#140864!$2#766,1#20!$2#765,1#3:!$2#764,1#65!$2#763,1#67!$2#762,1#61!$2#761,1#73!$2#760,1#75!$2#558,8^#?#???????<<<<<<<=!$2#560,8^#?#??????????>????!$2#598,8#<<<<<<<!$2#580,8#12889!$2#6>0,8$28!$2#590,8#6;3;40!$2#588,8#!$2#578,8+$2#750!$2#568,8+$2#7;0!$2#570,8+$2#858!$2#6>8,8$1;!$2#6?0,8$1:!$2#6?8,8$19!$2#700,8$18!$2#708,8$17!$2#710,8$16!$2#718,8#5!$2#720,8#6;4318!$2#728,8#1!$2#730,8#6;3;40!$2#738,8#164=1!$2#740,8#15;5:0!$2#748,8#140674!##15;5<0,8+$2#7;0!##15;5;0,8#!##15;5:8,8#!##15;5=8,8+$2#760!##15;628,4^#?#???????????????!##15;600,8#50!##15;5?8,8+$2#760!##15;5:0,4#5!$2#870,8#!$2#868,8#!$2#860,8#!$2#858,8#!$2#878,8#!$2#758,8+$2#900!$2#880,8$28!$2#888,8$15!$2#890,8$14!$2#898,8$13!$2#8:0,8+$2#900!$2#8:8,8#15;5:0!$2#8;0,8#164=1!$2#8;8,8#6?298!$2#20,8^#?#???????????????!$2#3?,1#!$2#3>,1#!$2#3=,1#!$2#3<,1#!$2#3;,1#!$2#3:,1#!$2#39,1#!$2#38,1#!$2#37,1#!$2#36,1#!$2#35,1#!$2#34,1#!$2#33,1#!$2#32,1#!$2#31,1#!$2#30,1#!$2#2?,1#!$2#2>,1#!$2#2=,1#!$2#2<,1#!$2#2;,1#!$2#2:,1#!$2#29,1#!$2#28,1#!$2#1?,1#!$2#1>,1#!$2#1=,1#!$2#1<,1#!$2#1;,1#!$2#1:,1#!$2#19,1#!$2#18,1#'$2#7???7?811000#800000000000&$2#10($2-380#<40,$2-380#398,$2#40#460,$2#4?0#8,$2#530#28,$2#5:8#138,$2#767#?1%#10000#158000'$21#7???7?811000#7?????????>?'$22##1????)$2-380#<40$21#+$22#1#&6$2#3#7???80=>#18!##7???:<98,8#(##15;5:0#4(##15;5:8#8(##15;5;0#8(##15;5<0#8(##15;5<8#8(##15;5=8#8(##15;5?8#8(##15;600#8(##15;628#4!##158<28,8#14056<!$2#8=8,8+$2#900!##6;3;40,8$28!##15;62<,4#????????!##15;630,4#????????!##160759,1#1!##15?:78,8#7???8000!##158=:0,8#148=68!$2#900,8$21,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 434840 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_5bdf21.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 451388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_5bdf21.IT BndT_Na_001.SegItab_Na_5bdf21.IT_sound BF NX0 BR XSTEP F0 PSS plan 451388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_duB.

End BndP_Na_050.
