(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002 BndT_Ns_001. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Ns_082.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_082 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_02b77c2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhM3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twhS3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_f5f21c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twr13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twr1C3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_effcfe2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_twsg3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082>LibSegNs_twtD13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_7efbb42ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJw3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082=LibSegNs_txJz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_082<LibSegNs_txK3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_twhM.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_02b77c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_02b77c.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#2!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#2='&9$2>#1#1#1'+&9$2>-2-1#19#2;'$2?#1000#7??????00000,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:"%pstring).
Definition ss0 : sym_state := SS 289856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0#5=#;>8;0,20##660>0+$2-110$3$4$5$6$7$2=#2?#30$2>#1#16$>$?$10$11#2#30#+@#2&6$2>#1-1#1+@#2&6$2>#1-1$18$19$1:$1;$1<$1=$1>$1?,,3<!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#2!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<:8!$2-60,8$26!$2-68,8$24!$2-70,8#2!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#198,$2-<0#48,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#2!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#2='&9$2>#1#1#1'+&9$2>-2-1#19#2;'$2?#1000#7??????00000,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 780464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_02b77c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_02b77c.IT BndT_Ns_000.SegItab_Ns_02b77c.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twhM.

Module LibSegNs_twhS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_02b77c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_02b77c.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#2!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##"%pstring).
Definition ss0 : sym_state := SS 289856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0#5=#;>8;0,20##660>0+$2-110$3$4$5$6$7$2=#2?#30@#100000000000000$31##16$>$?$10$11#2#30&6@#100000000000000$31#39#16#+@#2&6$31#1-1$18$19$1:$1;$1<$1=$1>$1?,,32!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#2!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<:8!$2-60,8$26!$2-68,8$24!$2-70,8#2!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#198,$2-<0#48,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#2!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 780464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_02b77c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_02b77c.IT BndT_Ns_000.SegItab_Ns_02b77c.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twhS.

Module LibSegNs_twr0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290264; 290296].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35#1#1?"%pstring).
Definition ss0 : sym_state := SS 290184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5;#46==0,20#$1+$2-<0$3$4$5$6$7$2=$22$2?++$2?$35-1#1$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35#1#1?,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5=#46==8,20#$1+$2-<0$3$4$5$6$7$2=$22+$2?#1++$2?$35-1#1$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?'&4$2?++$2?$35-1#1#1'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35#1#1?,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5=#46=?8,20#$1+$2-<0$3$4$5$6$7$2=$22$2?++$2?$35-1#1$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?'&4$2?++$2?$35-1##'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35#1#1?,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twr0.

Module LibSegNs_twr1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290264; 290296].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$37$38$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000,$38##1($38##1,$37-1#1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1"%pstring).
Definition ss0 : sym_state := SS 290264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 55), (-1), ELit 1); ((EVar 56), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 55), (-1), 1); ((EVar 56), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=?4,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$51$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$38#,1$51!$37-1,1$50'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1,52!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5=#46==8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$51$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4$37+$38-1#1#1!$38#,1$51!$37-1,1$50'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1,52!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5=#46=?8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$51$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4$37+$38-1##!$38#,1$51!$37-1,1$50'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1,52!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290264 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twr1.

Module LibSegNs_twr1C.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290264; 290296].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$37$38$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000,$38##1($38##1,$37-1#1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1!$37-1,1$39'$39##??!$38#,1$3:'$3:##??"%pstring).
Definition ss0 : sym_state := SS 290264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 55), (-1), ELit 1); ((EVar 56), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 55), (-1), 1); ((EVar 56), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=?4,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$39$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$38#,1$39!$37-1,1$3:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1'$39##??'$3:##??,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5=#46==8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$39$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4$37+$38-1#1#1!$38#,1$39!$37-1,1$3:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1'$39##??'$3:##??,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46==8#46=?8#5=#46=?8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$39$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4$37+$38-1##!$38#,1$39!$37-1,1$3:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1'$39##??'$3:##??,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290264 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twr1C.

Module LibSegNs_twsg.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290184].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20"%pstring).
Definition ss0 : sym_state := SS 290160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46=88#5;#46=78,20#$1+$2-<0$3$4$5$6$7$2=$22&9$25#2$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,22'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46=88#5=#46=88,20#$1+$2-<0$3$4$5$6$7$2=$22&9$25#2$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,23'&4&1&9$25#2##1#1#1'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46=88#5=#46=88,20##46=88+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,2>!+$2?$35#1,1#!+$2?$35#,1#2=!$2=#8,8+$35#1!$2-100,8$16!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=88'&4&1&9$25#2##1##'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290184 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twsg.

Module LibSegNs_twtD0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0!$2-;8,1#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-78,1$39'$39##??'&9$39#1#1#1!$2-68,8#8!$2-60,8$29'$29#1000#7??????00000!$2-8,8$28!$2-10,8$40!$2-18,8$41!$2-20,8$42!$2-28,8$43!$2-30,8$44!$2-38,8$45!$2-40,8$46!$2-48,8$47!$2-50,8$48!$2-58,8$49"%pstring).
Definition ss0 : sym_state := SS 290296 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#63=<4#5=#63=<4,20##46>58+$2-<0$3$4$5$6$7$2=$22$29#40$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0!$2-;8,1#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-78,1$39'$39##??'&9$39#1#1#1!$2-68,8#8!$2-60,8$29'$29#1000#7??????00000!$2-8,8$28!$2-10,8$40!$2-18,8$41!$2-20,8$42!$2-28,8$43!$2-30,8$44!$2-38,8$45!$2-40,8$46!$2-48,8$47!$2-50,8$48!$2-58,8$49,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 409028 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290296 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290296 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twtD0.

Module LibSegNs_twtD1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-<0$3$4$<=$<>$<?$2=$22$=2$=3$=4$=5$=6$=7$=8$=9+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$3:##??'&9$3:#1##'$39##??'&9$39#1#1#1!$2-;8,1#!$2-98,1$3:!$2-78,1$39!$2-68,8#8!$2-8,8$28!$2-10,8$40!$2-18,8$41!$2-20,8$42!$2-28,8$43!$2-30,8$44!$2-38,8$45!$2-40,8$46!$2-48,8$47!$2-50,8$48!$2-58,8$49,$2-2:0#1>0"%pstring).
Definition ss0 : sym_state := SS 290392 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46>88#5=#46>88,20#$28$2$3$4$<=$<>$<?$40$41$=2$=3$=4$=5$=6$=7$=8$=9$42$43$44$45$46$47$48$49$1:$1;$>4$>5$>6$>7,,18'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$3:##??'&9$3:#1##'$39##??'&9$39#1#1#1!$2-;8,1#!$2-98,1$3:!$2-78,1$39!$2-68,8#8!$2-8,8$28!$2-10,8$40!$2-18,8$41!$2-20,8$42!$2-28,8$43!$2-30,8$44!$2-38,8$45!$2-40,8$46!$2-48,8$47!$2-50,8$48!$2-58,8$49,$2-2:0#1>0,?;!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290392 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290392 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twtD1.

Module LibSegNs_txA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [271236].
Definition STOPS1 : list Z := [271236] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; ELit 7; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38'$;#7???7?800000#7??????????0!$;#,8$21!$;#8,8$22'$21##800000000000'$22##1?)$2-:0#:0$;##10'$>#7???7?800000#7??????????0"%pstring).
Definition ss0 : sym_state := SS 264408 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42384#42384#5=#42384,20##40:10+$2-:0$3$4$5$6$7$:$>$21$22+$2-38#7$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-20,8#!$2-28,8#!$2-30,8#!$2-38,1#!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38'$;#7???7?800000#7??????????0!$;#,8$21!$;#8,8$22'$21##800000000000'$22##1?)$2-:0#:0$;##10'$>#7???7?800000#7??????????0,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271236 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264408 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264408 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txA.

Module LibSegNs_txD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [271440] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?#1$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-160)) (ELit 160)].
Definition ss0 : sym_state := SS 264860 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-152), ELit 32); ((EVar 2), (-120), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-152), 32); ((EVar 2), (-120), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42450#42450#5=#42450,20##40:?4+$2-:0$3$4$5$6$7$:$2?+$2-38+$2-98+$2-58+$2-78#1$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$2-80,8#!$2-88,8#3;9:<:00!$2-90,8#1!$2-98,1#!$2-60,8#!$2-68,8#!$2-70,8#!$2-78,1#!$2-40,8#!$2-48,8#!$2-50,8#!$2-58,1#'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264860 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264860 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txD.

Module LibSegNs_txF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [268884].
Definition STOPS1 : list Z := [268884] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37#16$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483232 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 264720 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:54#41:54#5=#41:54,20##40:24+$2-:0$3$4$5$6$7$:$2?$2?#:$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'$2#7???7?8000:0#800000000000&$2#10,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 268884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264720 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264720 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txF.

Module LibSegNs_txJw.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [264740].
Definition STOPS1 : list Z := [264740] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?8000:0#800000000000&$2#10!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##"%pstring).
Definition ss0 : sym_state := SS 265232 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40:24#40:24#5=#40:24,20#$1+$2-:0$3$4$5$6$7$:$2?#$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?8000:0#800000000000&$2#10!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264740 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265232 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 265232 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txJw.

Module LibSegNs_txJz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [264740].
Definition STOPS1 : list Z := [264740] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483232 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 265044 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40:24#40:24#5=#40:24,20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'$2#7???7?8000:0#800000000000&$2#10,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264740 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 265044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txJz.

Module LibSegNs_txK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [271324].
Definition STOPS1 : list Z := [271324] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37#$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483232 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 264720 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=<#423=<#5=#423=<,20##40:9<+$2-:0$3$4$5$6$7$:$2?+$2-38#$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'$2#7???7?8000:0#800000000000&$2#10,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271324 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264720 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264720 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txK.

End BndP_Ns_082.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_000 BndT_Ns_001.
Module BndP_Ns_075.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_000 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_075 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bebaca2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b11p3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b20p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075ALibSegNs_teV2b21p3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_18bef92ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12a03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12bz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12c03kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_96076c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cP3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12cZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075>LibSegNs_ts12e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_075?LibSegNs_ts12qD3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_teV2b11p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##42704+$2-130$3$4$5$6$7$2;+$2#48+$2#48$32$33$34$35$36+$2-78$37##3;9:<:00#+$2-78+$2-98+$2#78+$2#58$19#+$2#28$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,52!$2#28,1#!$2#48,1#!$2#38,8$2;!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#1!$2-<8,1#!$2#50,8#1'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;#1^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2b11p.

Module LibSegNs_teV2b20n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##42704+$2-130$3$4$5$6$7$2;+$2#48+$2#48$32$33$34$35$36+$2-78$37##3;9:<:00#1+$2-78+$2-98+$2#78+$2#58$19#2+$2#28$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;##"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9##2#2+$2#58+$2#60$2:+$2-78$37$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,52!$2#28,1#2!$2#48,1#2!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#1!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#!$2-<8,1#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2b20n.

Module LibSegNs_teV2b20p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##42704+$2-130$3$4$5$6$7$2;+$2#48+$2#48$32$33$34$35$36+$2-78$37##3;9:<:00#+$2-78+$2-98+$2#78+$2#58$19#+$2#28$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;##"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9###2+$2#58+$2#60$2:+$2-78$37$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,52!$2#28,1#!$2#48,1#!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#!$2-<8,1#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2b20p.

Module LibSegNs_teV2b21n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##42704+$2-130$3$4$5$6$7$2;+$2#48+$2#48$32$33$34$35$36+$2-78$37##3;9:<:00#1+$2-78+$2-98+$2#78+$2#58$19#2+$2#28$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##2$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,52!$2#28,1#2!$2#48,1#2!$2#38,8$2;!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#1!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#1!$2-<8,1#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;#1^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2b21n.

Module LibSegNs_teV2b21p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##42704+$2-130$3$4$5$6$7$2;+$2#48+$2#48$32$33$34$35$36+$2-78$37##3;9:<:00#+$2-78+$2-98+$2#78+$2#58$19#+$2#28$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 128)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 128)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,52!$2#28,1#!$2#48,1#!$2#38,8$2;!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#1!$2-<8,1#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#^#?#???????????????'$2:#1^#?#???????????????'$2;#1^#?#???????????????,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2b21p.

Module LibSegNs_ts12a0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [287388].
Definition STOPS1 : list Z := [287388] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26#4$;$<$=$>$?$10$11$25+$24#18#4#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$23##????????!$2-6<,4$23"%pstring).
Definition ss0 : sym_state := SS 286544 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4629<#4629<#5=#4629<,20##45?6<+$2-90$3$4$5$6$7$24$26+$24#18+$2-48#8$=$>$?$10$11$25+$24#18$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$23##????????!$2-6<,4$23,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 287388 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286544 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286544 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12a0.

Module LibSegNs_ts12bn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [279660].
Definition STOPS1 : list Z := [279660] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26#8$;$<$=$>$?$10$11$25+$24#18$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-48,8$32'$32#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 286572 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-104), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-104), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4446<#4446<#5=#4446<,20##46010+$2-90$3$4$5$6$7$24$26+$2-68#3;9:<:00&7&8&8+@#100000000000000$32@#10000000000&9$32#??00&8@#1000000&9$32#??0000@#100000000%6$32#18+&6$32#38+&9&6$32#18#??0000+&9&6$32#28#??00@#1000000%6&6$32#8#18#3?&8+@#100000000000000$32@#10000000000&9$32#??00&8@#1000000&9$32#??0000@#100000000%6$32#18&9&6$32#6#2@#1000000%6&6$32#8#18$10$11$25#??00$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$2-50,8#!$2-58,8+&5&8&8+@#100000000000000$32@#10000000000&9$32#??00&8@#1000000&9$32#??0000@#100000000%6$32#18+&6$32#38+&9&6$32#18#??0000+&9&6$32#28#??00@#1000000%6&6$32#8#18&7&8&8+@#100000000000000$32@#10000000000&9$32#??00&8@#1000000&9$32#??0000@#100000000%6$32#18+&6$32#38+&9&6$32#18#??0000+&9&6$32#28#??00@#1000000%6&6$32#8#18#3?@-1&7&8&8+@#100000000000000$32@#10000000000&9$32#??00&8@#1000000&9$32#??0000@#100000000%6$32#18+&6$32#38+&9&6$32#18#??0000+&9&6$32#28#??00@#1000000%6&6$32#8#18#3?!$2-60,8#1!$2-68,1&9&6$32#6#2'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-48,8$32'$32#1^#?#???????????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 279660 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12bn.

Module LibSegNs_ts12bz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [279660].
Definition STOPS1 : list Z := [279660] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26#8$;$<$=$>$?$10$11$25+$24#18$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-48,8#"%pstring).
Definition ss0 : sym_state := SS 286572 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-104), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-104), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4446<#4446<#5=#4446<,20##46010+$2-90$3$4$5$6$7$24$26+$2-68#3;9:<:00####$10$11$25#??00$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-50,8#!$2-58,8#!$2-60,8#!$2-68,1#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-48,8#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 279660 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12bz.

Module LibSegNs_ts12c0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [286772].
Definition STOPS1 : list Z := [286772] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25#??00$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1"%pstring).
Definition ss0 : sym_state := SS 286736 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46034#46034#5=#46034,20#$1+$2-90$3$4$5$6$7$24$26&8&9&6$23#8#??00&6$23#18&8%2$23#18@#100&9$23#??00@#100&9$23#??00$=$>$?$10$11$25&8&8%2$23#18@#100&9$23#??00&8&9&6$23#8#??00&6$23#18$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 286772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286736 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286736 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12c0.

Module LibSegNs_ts12cN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_96076c.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_96076c.IT.
Definition ENDS : list Z := [276616].
Definition STOPS1 : list Z := [276616] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$24#7???7?8000<0#7????????>70&$24#8)$2-<0#<0$24##190'$26#7???7?8000<0#7??????????0&$26#8)$2-<0#<0$26##10'$25#7???7?8000<0#7?????????:0&$25#8)$2-<0#<0$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-68,1#2!$2-60,8$34!$2-58,8$35!$2-50,8$36($2-68#20'$34#1#2"%pstring).
Definition ss0 : sym_state := SS 286772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 2), (-144), ELit 32); ((EVar 2), (-104), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 2), (-144), 32); ((EVar 2), (-104), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43888#43888#5=#43888,20##4606<+$2-90$3$4$5$6$7$24$26+$2-68+$2-90+$2-58#1$34#+$2-;0#$25@#100000000$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$2-78,8#!$2-80,8&6@#100000000$37#20!$2-88,8&4#$23!$2-90,1#!$2-:8,8#!$2-;0,8#!$2-;8,8#!$2-<0,1#!$2-:0,8$24!$2-98,8#46040'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$24#7???7?8000<0#7????????>70&$24#8)$2-<0#<0$24##190'$26#7???7?8000<0#7??????????0&$26#8)$2-<0#<0$26##10'$25#7???7?8000<0#7?????????:0&$25#8)$2-<0#<0$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-68,1#2!$2-60,8$34!$2-58,8$35!$2-50,8$36($2-68#20'$34#1#2,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 276616 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_96076c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_96076c.IT BndT_Ns_001.SegItab_Ns_96076c.IT_sound BF NX0 BR XSTEP F0 PSS plan 286772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12cN.

Module LibSegNs_ts12cP.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_96076c.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_96076c.IT.
Definition ENDS : list Z := [290684].
Definition STOPS1 : list Z := [290684] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$24#7???7?8000<0#7????????>70&$24#8)$2-<0#<0$24##190'$26#7???7?8000<0#7??????????0&$26#8)$2-<0#<0$26##10'$25#7???7?8000<0#7?????????:0&$25#8)$2-<0#<0$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-68,1#!$2-60,8$34!$2-58,8$35!$2-50,8$36($2-68#20'$34#1#2"%pstring).
Definition ss0 : sym_state := SS 286772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 2), (-104), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 2), (-104), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46?7<#46?7<#5=#46?7<,20##461;<+$2-90$3$4$5$6$7$24$26+$2-68$37+$2-58#$34#+$2-;0#$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-:8,8#!$2-;0,8#!$2-;8,8#!$2-<0,1#!$2-:0,8$24!$2-98,8#46040'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$24#7???7?8000<0#7????????>70&$24#8)$2-<0#<0$24##190'$26#7???7?8000<0#7??????????0&$26#8)$2-<0#<0$26##10'$25#7???7?8000<0#7?????????:0&$25#8)$2-<0#<0$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-68,1#!$2-60,8$34!$2-58,8$35!$2-50,8$36($2-68#20'$34#1#2,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290684 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_96076c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_96076c.IT BndT_Ns_001.SegItab_Ns_96076c.IT_sound BF NX0 BR XSTEP F0 PSS plan 286772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12cP.

Module LibSegNs_ts12cZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_96076c.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_96076c.IT.
Definition ENDS : list Z := [290684].
Definition STOPS1 : list Z := [290684] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$24#7???7?8000<0#7????????>70&$24#8)$2-<0#<0$24##190'$26#7???7?8000<0#7??????????0&$26#8)$2-<0#<0$26##10'$25#7???7?8000<0#7?????????:0&$25#8)$2-<0#<0$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-68,1#!$2-60,8#!$2-58,8#!$2-50,8#($2-68#20"%pstring).
Definition ss0 : sym_state := SS 286772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 2), (-104), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 2), (-104), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46?7<#46?7<#5=#46?7<,20##461;<+$2-90$3$4$5$6$7$24$26+$2-68$37+$2-58###+$2-;0#$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$2-:8,8#!$2-;0,8#!$2-;8,8#!$2-<0,1#!$2-:0,8$24!$2-98,8#46040'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$24#7???7?8000<0#7????????>70&$24#8)$2-<0#<0$24##190'$26#7???7?8000<0#7??????????0&$26#8)$2-<0#<0$26##10'$25#7???7?8000<0#7?????????:0&$25#8)$2-<0#<0$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-68,1#!$2-60,8#!$2-58,8#!$2-50,8#($2-68#20,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290684 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_96076c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_96076c.IT BndT_Ns_001.SegItab_Ns_96076c.IT_sound BF NX0 BR XSTEP F0 PSS plan 286772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12cZ.

Module LibSegNs_ts12e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [268884].
Definition STOPS1 : list Z := [268884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$31$;$<$=$>$?$10$11$25+$24#18$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$31##7"%pstring).
Definition ss0 : sym_state := SS 286572 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:54#41:54#5=#41:54,20##4609<+$2-90$3$4$5$6$7$24$26$26#1$<$=$>$?$10$11$25+$24#18$23#8$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$31##7,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 268884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12e.

Module LibSegNs_ts12qD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#10,1#!$2-68,1$21'$21##??'&9$21#1#1#1!$2-58,8$35!$2-50,8$36'$36#1^#?#???????????????'$35##400"%pstring).
Definition ss0 : sym_state := SS 287288 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##461:<+$2-90$3$4$5$6$7$24$26$36@#8$35$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$24#8,1#1'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#10,1#!$2-68,1$21'$21##??'&9$21#1#1#1!$2-58,8$35!$2-50,8$36'$36#1^#?#???????????????'$35##400,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 409028 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287288 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12qD.

End BndP_Ns_075.
Module BndP_Ns_077.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_077 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_18bef92ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_ts8dS3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_f28ec62ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsA32_13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_b5d8002ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2a3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_da0d922ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077ALibSegNs_tsA32_2b3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_846d302ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsAdd13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bcd1ea2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivA13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077@LibSegNs_tsDivBb3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_73ac7b2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077?LibSegNs_tsMul13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_1ffdf72ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_077>LibSegNs_tsRzA3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ts8dS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [244020].
Definition STOPS1 : list Z := [244020] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1##"%pstring).
Definition ss0 : sym_state := SS 287024 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-144), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;934#3;934#5=#3;934,20##46180+$2-90$3$4$5$6$7$24$26$25+$2-90#7$24$26#3;934$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$2-88,8&6$21#1!$2-90,8+$24#149'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 244020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8dS.

Module LibSegNs_tsA32_0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f28ec6.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f28ec6.IT.
Definition ENDS : list Z := [291004].
Definition STOPS1 : list Z := [291004] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 35; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#($22##20"%pstring).
Definition ss0 : sym_state := SS 290684 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5;#43860,20##470:8+$2-60$3$4$5$6$7$22@#100000000$23$22##1+$22#10+$22#10&6@#100000000$23#20$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$22#10,8&6@#100000000$23#20!$22#18,8#!$22#8,8#1!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#!$2-;8,8#1!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#($22##20,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22##+$22#10+$22#8&6@#100000000$23#20$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$22#,1#!$22#8,8#'&4&1&6@#100000000$23#20##1#1#1!$22#10,8&6@#100000000$23#20!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#!$2-;8,8#1!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20($22##20,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22##1+$22#10+$22#10&6@#100000000$23#20$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4&1&6@#100000000$23#20##1##!$22#10,8&6@#100000000$23#20!$22#18,8#!$22#8,8#1!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#!$2-;8,8#1!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#($22##20,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f28ec6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290684 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f28ec6.IT BndT_Ns_002.SegItab_Ns_f28ec6.IT_sound BF NX0 BR XSTEP F0 PSS plan 290684 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsA32_0.

Module LibSegNs_tsA32_1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f28ec6.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f28ec6.IT.
Definition ENDS : list Z := [291004].
Definition STOPS1 : list Z := [291004] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 35; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#!$22#8,8#1!$22#10,8$24!$22#18,8#($22##20'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 290684 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5;#47074,20##46?;0+$2-60$3$4$5$6$7$22@#100000000$23#2+$22#10&4+$24&6@#100000000$23#20$24+$24&6@#100000000$23#20#2$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$22#10,8+$24&6@#100000000$23#20!$22#18,8#!$22#8,8#2!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#($22##20'$24#1^#?#???????????????,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5;#43860,20##470:8+$2-60$3$4$5$6$7$22@#100000000$23$22##1+$22#10+$22#10+$24&6@#100000000$23#20$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$22#8,8#1'&4&1&4+$24&6@#100000000$23#20$24##1#1#1!$22#10,8+$24&6@#100000000$23#20!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#($22##20'$24#1^#?#???????????????,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22##+$22#10+$22#8+$24&6@#100000000$23#20$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$22#,1#!$22#8,8#'&4&1+$24&6@#100000000$23#20##1#1#1'&4&1&4+$24&6@#100000000$23#20$24##1#1#1!$22#10,8+$24&6@#100000000$23#20!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20($22##20'$24#1^#?#???????????????,40!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22##1+$22#10+$22#10+$24&6@#100000000$23#20$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1='&4&1+$24&6@#100000000$23#20##1##!$22#8,8#1'&4&1&4+$24&6@#100000000$23#20$24##1#1#1!$22#10,8+$24&6@#100000000$23#20!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#($22##20'$24#1^#?#???????????????,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22##2+$22#10+$22#18#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$22#18,8#1'&4&1&4+$24&6@#100000000$23#20$24##1##!$22#10,8+$24&6@#100000000$23#20!$22#8,8#2!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#46?;0!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1#($22##20'$24#1^#?#???????????????,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f28ec6.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290684 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f28ec6.IT BndT_Ns_002.SegItab_Ns_f28ec6.IT_sound BF NX0 BR XSTEP F0 PSS plan 290684 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsA32_1.

Module LibSegNs_tsA32_2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_b5d800.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_b5d800.IT.
Definition ENDS : list Z := [275516].
Definition STOPS1 : list Z := [275516] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 35; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800060#800000000000&$2#10($2-60#60%#10000#<6<<0'$22#7???7?800060#7?????????>0&$22#8)$2-60#60$22##20!$22#,1#!$22#8,8#2!$22#10,8$24!$22#18,8$26($22##20"%pstring).
Definition ss0 : sym_state := SS 290684 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-96), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4343<#4343<#5=#4343<,20##46?;0+$2-60$3$4$5$6$7$22$23$22#3$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800060#800000000000&$2#10($2-60#60%#10000#<6<<0'$22#7???7?800060#7?????????>0&$22#8)$2-60#60$22##20!$22#,1#!$22#8,8#2!$22#10,8$24!$22#18,8$26($22##20,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 275516 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_b5d800.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290684 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_b5d800.IT BndT_Ns_001.SegItab_Ns_b5d800.IT_sound BF NX0 BR XSTEP F0 PSS plan 290684 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsA32_2a.

Module LibSegNs_tsA32_2b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_da0d92.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_da0d92.IT.
Definition ENDS : list Z := [291004].
Definition STOPS1 : list Z := [291004] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4$5$6$7$22$23$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800060#800000000000&$2#10($2-60#60%#10000#<6<<0'$22#7???7?800060#7?????????>0&$22#8)$2-60#60$22##20!$22#,1#1!$22#8,8#3!$22#10,8#8!$22#18,8$29($22##20'$29#1000#7??????00000&$29#10($29##40,$29#18#28!$29#,8$24!$29#8,8$26!$29#10,8#)$29##40$22##20)$2-60#60$29##40'$26#1^#4#!$2-8,8$28!$2-10,8$8!$2-18,8$9"%pstring).
Definition ss0 : sym_state := SS 290736 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-96), ELit 96); ((EVar 34), (0), ELit 32); ((EVar 41), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-96), 96); ((EVar 34), (0), 32); ((EVar 41), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5;#47074,20#$1+$2-60$3$4$5$6$7$22@#100000000$23#3$29&4+$24&6@#100000000$23#20$24+$24&6@#100000000$23#20#2$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$29#,8+$24&6@#100000000$23#20'$2#7???7?800060#800000000000&$2#10($2-60#60'$22#7???7?800060#7?????????>0&$22#8)$2-60#60$22##20!$22#,1#1!$22#8,8#3!$22#10,8#8!$22#18,8$29($22##20'$29#1000#7??????00000&$29#10($29##40,$29#18#28!$29#8,8$26!$29#10,8#)$29##40$22##20)$2-60#60$29##40'$26#1^#4#!$2-8,8$28!$2-10,8$8!$2-18,8$9,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22#1#2$29+$29#8$26$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$22#8,8#2'&4&1&4+$24&6@#100000000$23#20$24##1#1#1!$29#,8+$24&6@#100000000$23#20'$2#7???7?800060#800000000000&$2#10($2-60#60'$22#7???7?800060#7?????????>0&$22#8)$2-60#60$22##20!$22#,1#1!$22#10,8#8!$22#18,8$29($22##20'$29#1000#7??????00000&$29#10($29##40,$29#18#28!$29#8,8$26!$29#10,8#)$29##40$22##20)$2-60#60$29##40'$26#1^#4#!$2-8,8$28!$2-10,8$8!$2-18,8$9,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#470;<#470;<#5=#470;<,20#$28$2$3$4$5$6$7$8$9$22#1#2$29+$29#8+$26#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$22#8,8#2!$29#8,8+$26#1'&4&1&4+$24&6@#100000000$23#20$24##1##!$29#,8+$24&6@#100000000$23#20'$2#7???7?800060#800000000000&$2#10($2-60#60'$22#7???7?800060#7?????????>0&$22#8)$2-60#60$22##20!$22#,1#1!$22#10,8#8!$22#18,8$29($22##20'$29#1000#7??????00000&$29#10($29##40,$29#18#28!$29#10,8#)$29##40$22##20)$2-60#60$29##40'$26#1^#4#!$2-8,8$28!$2-10,8$8!$2-18,8$9,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 291004 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_da0d92.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290736 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_da0d92.IT BndT_Ns_002.SegItab_Ns_da0d92.IT_sound BF NX0 BR XSTEP F0 PSS plan 290736 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsA32_2b.

Module LibSegNs_tsAdd0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_846d30.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_846d30.IT.
Definition ENDS : list Z := [275256].
Definition STOPS1 : list Z := [275256] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 35; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25!$22#8,8#!$22#10,8#!$22#18,8#($22##20'$25##??'&9$25#1##'&9$25#2##"%pstring).
Definition ss0 : sym_state := SS 274952 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5;#43860,20##43324+$2-60$3$4$5$6$7$22$23$22$25#1+$22#10+$22#10$23$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$22#10,8$23!$22#18,8#!$22#8,8#1!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#!$2-;8,8#1!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5=#43338,20#$28$2$3$4$5$6$7$8$9$22&9$25#?=#+$22#10+$22#8$23$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$22#,1&9$25#?=!$22#8,8#'&4&1$23##1#1#1!$22#10,8$23!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#!$2-;8,8#1!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5=#43338,20#$28$2$3$4$5$6$7$8$9$22$25#1+$22#10+$22#10$23$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>'&4&1$23##1##!$22#10,8$23!$22#18,8#!$22#8,8#1!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#!$2-;8,8#1!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 275256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 275256 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_846d30.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274952 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_846d30.IT BndT_Ns_001.SegItab_Ns_846d30.IT_sound BF NX0 BR XSTEP F0 PSS plan 274952 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsAdd0.

Module LibSegNs_tsAdd1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_846d30.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_846d30.IT.
Definition ENDS : list Z := [275256].
Definition STOPS1 : list Z := [275256] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 35; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25!$22#8,8#1!$22#10,8$24!$22#18,8#($22##20'$25##??'&9$25#1##'&9$25#2##"%pstring).
Definition ss0 : sym_state := SS 274952 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5;#432?0,20##4323<+$2-60$3$4$5$6$7$22+$23$24#2+$22#10&4+$23$24$24#2$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$22#10,8+$23$24!$22#18,8#!$22#8,8#2!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5;#43860,20##43324+$2-60$3$4$5$6$7$22+$23$24$22$25#1+$22#10+$22#10+$23$24$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$22#8,8#1'&4&1&4+$23$24$24##1#1#1!$22#10,8+$23$24!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5=#43338,20#$28$2$3$4$5$6$7$8$9$22&9$25#?=#+$22#10+$22#8+$23$24$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$22#,1&9$25#?=!$22#8,8#'&4&1+$23$24##1#1#1'&4&1&4+$23$24$24##1#1#1!$22#10,8+$23$24!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5=#43338,20#$28$2$3$4$5$6$7$8$9$22$25#1+$22#10+$22#10+$23$24$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?'&4&1+$23$24##1##!$22#8,8#1'&4&1&4+$23$24$24##1#1#1!$22#10,8+$23$24!$22#18,8#!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43338#43338#5=#43338,20#$28$2$3$4$5$6$7$8$9$22$25#2+$22#10+$22#18#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$22#18,8#1'&4&1&4+$23$24$24##1##!$22#10,8+$23$24!$22#8,8#2!$2-=8,8$15!$2-=0,8$14!$2-<8,8$13!$2-<0,8#1!$2-;8,8#2!$2-;0,8$22!$2-:8,8#43460!$2-80,8$12!$2-78,8$23!$2-70,8$22!$2-68,8#4323<!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000>0#800000000000&$2#10($2->0#>0%#10000#<6<<0'$22#7???7?8000>0#7?????????>0&$22#8)$2->0#>0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##'&9$25#2##,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SR.PS 275256 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 275256 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 275256 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_846d30.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274952 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_846d30.IT BndT_Ns_001.SegItab_Ns_846d30.IT_sound BF NX0 BR XSTEP F0 PSS plan 274952 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsAdd1.

Module LibSegNs_tsDivA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bcd1ea.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bcd1ea.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8$24!$2#60,8$26'$25##??'&9$25#1##'$24#1^#8#:<7230489>7????'$2;##??'&9$2;#1##"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$43$44$45$8$9#$47$48$49$4:$4;$4<$4=$12$13$14$15$16$17$18$19$1:$1;$4>$4?$50$51,,46!$2#28,1&8&9$2;#?=&9$25#2!$2#38,8$24!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8&9+&9$25#2&9$41#?<#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42580!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1&9$40#?<!$2-:8,1&9+&9$25#2&9$41#?<#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-1:0#20,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8$24!$2#60,8$26'$25##??'&9$25#1##'$24#1^#8#:<7230489>7????'$2;##??'&9$2;#1##,52!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bcd1ea.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bcd1ea.IT BndT_Ns_002.SegItab_Ns_bcd1ea.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsDivA0.

Module LibSegNs_tsDivA1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bcd1ea.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bcd1ea.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#1!$2#38,8$2<!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8$24!$2#60,8$26'$25##??'&9$25#1##'$24#1^#8#:<7230489>7????'$2;##??'&9$2;#1##"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$43$44$45$8$9#$47$48$49$4:$4;$4<$4=$12$13$14$15$16$17$18$19$1:$1;$4>$4?$50$51,,46!$2#28,1&8&9$2;#?=&9$25#2!$2#38,8$24!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8&9+&9$25#2&9$41#?<#?=!$2-1<8,8+$2-:8!$2-1<0,8#1!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42580!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1&9$40#?<!$2-:8,1&9+&9$25#2&9$41#?<#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-1:0#20,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#40,8#!$2#58,8$24!$2#60,8$26'$25##??'&9$25#1##'$24#1^#8#:<7230489>7????'$2;##??'&9$2;#1##,52!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bcd1ea.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bcd1ea.IT BndT_Ns_002.SegItab_Ns_bcd1ea.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsDivA1.

Module LibSegNs_tsDivBa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bcd1ea.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bcd1ea.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8$24!$2#60,8$26'$25##??'&9$25#1##'$24^#8#:<7230489>80001^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5;#43464,20##43460+$2-1:0$3$4$43$44$45+$2#28&4#/7$24^#8#:<7230489>80000###2$49$4:$4;$4<$4=#+$2-<8#+$2-78+$2-98+$2#58+$2#58$19&9$25#2+$2#28$4>$4?$50$51,,46!$2#30,8&4#/7$24^#8#:<7230489>80000!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24^#8#:<7230489>80000!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24^#8#:<7230489>80000!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24^#8#:<7230489>80000!$2-<0,8&4#/7$24^#8#:<7230489>80000!$2-<8,1#!$2#58,8/5$24^#8#:<7230489>80000!$2#48,1&9$25#?=!$2#50,8#1!$2-100,8#1!$2-88,1&9$40#?<!$2-:8,1&9+&9$25#2&9$41#?<#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1#!$2#38,8#!$2#40,8#!$2#60,8$26'$25##??'&9$25#1##'$24^#8#:<7230489>80001^#?#???????????????,52!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ce2 : expr := EMd Instr.M_REMU (EVar 36) (ELit 10000000000000000000).
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$43$44$45$8$9#@#2&6&5#&9$25#2#1#2$49$4:$4;$4<$4=$12$13$14$15$16$17$18$19$1:$1;$4>$4?$50$51,,47!$2#28,1&9$25#2!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1'/7$24^#8#:<7230489>80000##!$2#30,8&4#/7$24^#8#:<7230489>80000!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24^#8#:<7230489>80000!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24^#8#:<7230489>80000!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24^#8#:<7230489>80000!$2-<0,8&4#/7$24^#8#:<7230489>80000!$2-<8,1#!$2#58,8/5$24^#8#:<7230489>80000!$2#50,8#1!$2-100,8#1!$2-88,1&9$40#?<!$2-:8,1&9+&9$25#2&9$41#?<#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#38,8#!$2#40,8#!$2#60,8$26'$25##??'&9$25#1##'$24^#8#:<7230489>80001^#?#???????????????,52!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$53$54$55$8$9#@#2&6&5#&9$25#2#1$58$59$5:$5;$5<$5=$12$13$14$15$16$17$18$19$1:$1;$5>$5?$60$61,,47!$2#28,1&9$25#2!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#38,8/7$24^#8#:<7230489>80000!$2#40,8#'/7$24^#8#:<7230489>80000#1^#8#:<7230489>7????!$2#30,8&4#/7$24^#8#:<7230489>80000!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24^#8#:<7230489>80000!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24^#8#:<7230489>80000!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24^#8#:<7230489>80000!$2-<0,8&4#/7$24^#8#:<7230489>80000!$2-<8,1#!$2#58,8/5$24^#8#:<7230489>80000!$2#50,8#1!$2-100,8#1!$2-88,1&9$40#?<!$2-:8,1&9+&9$25#2&9$41#?<#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#60,8$26'$25##??'&9$25#1##'$24^#8#:<7230489>80001^#?#???????????????,62!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PCase ce2 (0) (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bcd1ea.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bcd1ea.IT BndT_Ns_002.SegItab_Ns_bcd1ea.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsDivBa.

Module LibSegNs_tsDivBb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bcd1ea.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bcd1ea.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8^#8#:<7230489>80000!$2#60,8$26'$25##??'&9$25#1##"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$43$44$45$8$9#@#2&6&5#&9$25#2#1#2$49$4:$4;$4<$4=$12$13$14$15$16$17$18$19$1:$1;$4>$4?$50$51,,45!$2#28,1&9$25#2!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42634!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2#58,8#1!$2#50,8#1!$2-100,8#1!$2-88,1&9$40#?<!$2-:8,1&9+&9$25#2&9$41#?<#?=!$2-90,8$26!$2-98,8^#8#:<7230489>80000!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#38,8#!$2#40,8#!$2#60,8$26'$25##??'&9$25#1##,52!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bcd1ea.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bcd1ea.IT BndT_Ns_002.SegItab_Ns_bcd1ea.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsDivBb.

Module LibSegNs_tsMul0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_73ac7b.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_73ac7b.IT.
Definition ENDS : list Z := [279948].
Definition STOPS1 : list Z := [279948] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; ELit 1000000000; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20!$22#,1$25!$22#8,8#!$22#10,8#!$22#18,8#($22##20'$25##??'&9$25#1##"%pstring).
Definition ss0 : sym_state := SS 279660 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4458<#4458<#5=#4458<,20#$28$2$3$4$5$6$7$8$9$22&9$25#?=#+$22#10+$22#8#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$22#,1&9$25#?=!$22#8,8#!$22#10,8#!$22#18,8#!$2-:8,8$15!$2-:0,8#!$2-98,8#!$2-90,8#!$2-88,8#1!$2-80,8$22!$2-78,8#43460!$2-50,8+$22#10!$2-48,8#3;9:<:00!$2-40,8$22!$2-38,8#444;<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20($22##20'$25##??'&9$25#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 279948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_73ac7b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 279660 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_73ac7b.IT BndT_Ns_001.SegItab_Ns_73ac7b.IT_sound BF NX0 BR XSTEP F0 PSS plan 279660 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsMul0.

Module LibSegNs_tsMul1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_73ac7b.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_73ac7b.IT.
Definition ENDS : list Z := [279948].
Definition STOPS1 : list Z := [279948] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; ELit 1000000000; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20!$22#,1$25!$22#8,8#1!$22#10,8$24!$22#18,8#($22##20'$25##??'&9$25#1##"%pstring).
Definition ss0 : sym_state := SS 279660 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 176); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-176), 176); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4458<#4458<#5;#43860,20##4456<+$2-30$3$4#&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????#$22#3;9:<:00$22$25#2+$22#10+$22#18+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20+$22#20&6@#3;9:<:00&6$24#20#20+$22#10##1$15$16$17$18$19$1:$1;#@#3;9:<:00&9$24#????????$1>$1?,,1?!$22#18,8+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20!$22#10,8+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????!$22#8,8#2!$2-:8,8$15!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8+$22#10!$2-48,8#3;9:<:00!$2-40,8$22!$2-38,8#444;<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition s3 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#43860,20##4456<+$2-30$3$4#&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????#$22#3;9:<:00$22$25#1+$22#10+$22#10+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????+$22#20&6@#3;9:<:00&6$24#20#20+$22#10##1$15$16$17$18$19$1:$1;#@#3;9:<:00&9$24#????????$1>$1?,,20!$22#8,8#1'&4&1+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20##1#1#1!$22#18,8+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20!$22#10,8+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????!$2-:8,8$15!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8+$22#10!$2-48,8#3;9:<:00!$2-40,8$22!$2-38,8#444;<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##,40!"%pstring).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4458<#4458<#5=#4458<,20#$28$2$3$4#&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????#$8$9$22&9$25#?=#+$22#10+$22#8+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????+$22#20&6@#3;9:<:00&6$24#20#20$12$13$14$15$16$17$18$19$1:$1;#@#3;9:<:00&9$24#????????$1>$1?,,21!$22#,1&9$25#?=!$22#8,8#'&4&1+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????##1#1#1'&4&1+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20##1#1#1!$22#18,8+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20!$22#10,8+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????!$2-:8,8$15!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8+$22#10!$2-48,8#3;9:<:00!$2-40,8$22!$2-38,8#444;<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20($22##20'$25##??'&9$25#1##,40!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4458<#4458<#5=#4458<,20#$28$2$3$4#&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????#$8$9$22$25#1+$22#10+$22#10+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????+$22#20&6@#3;9:<:00&6$24#20#20$12$13$14$15$16$17$18$19$1:$1;#@#3;9:<:00&9$24#????????$1>$1?,,21'&4&1+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????##1##!$22#8,8#1'&4&1+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20##1#1#1!$22#18,8+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20!$22#10,8+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????!$2-:8,8$15!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8+$22#10!$2-48,8#3;9:<:00!$2-40,8$22!$2-38,8#444;<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4458<#4458<#5=#4458<,20#$28$2$3$4#&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????#$8$9$22$25#2+$22#10+$22#18+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20+$22#20&6@#3;9:<:00&6$24#20#20$12$13$14$15$16$17$18$19$1:$1;#@#3;9:<:00&9$24#????????$1>$1?,,20'&4&1+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20##1##!$22#18,8+&4+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????@#3;9:<:00&9$24#????????&6@#3;9:<:00&6$24#20#20!$22#10,8+@^#3#;9:<:0000000000&6$24#20@#3;9:<:00&9$24#????????!$22#8,8#2!$2-:8,8$15!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8+$22#10!$2-48,8#3;9:<:00!$2-40,8$22!$2-38,8#444;<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000;0#800000000000&$2#10($2-;0#;0%#10000#<6<<0'$22#7???7?8000;0#7?????????>0&$22#8)$2-;0#;0$22##20!$22#,1$25($22##20'$25##??'&9$25#1##,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SR.PS 279948 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 279948 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 279948 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_73ac7b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 279660 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_73ac7b.IT BndT_Ns_001.SegItab_Ns_73ac7b.IT_sound BF NX0 BR XSTEP F0 PSS plan 279660 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsMul1.

Module LibSegNs_tsRzA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_1ffdf7.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_1ffdf7.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; ELit 3; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?8000?0#800000000000&$2#10($2-?0#?0%#10000#<6<<0'$22#7???7?8000?0#7?????????>0&$22#8)$2-?0#?0$22##20!$22#,1$25!$22#8,8#2!$22#10,8$24!$22#18,8$26($22##20'$25##??'&9$25#1##"%pstring).
Definition ss0 : sym_state := SS 275516 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 240); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-240), 240); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##436:0+$2-<0$3$4$5$6$7$22#8#40^#1#??????????????:^#1#??????????????7$=$>$?$10$11$24$26&9$25#2#2$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$2-=8,8#3!$2-=0,8$22!$2-<8,8#4368<!$2-:8,8$26!$2-:0,8$24!$2-98,8#3!$2-90,8$22!$2-88,8#435=<!$22#18,8#!$22#10,8#!$22#8,8#!$22#,1+@#4&6$25#2#1!$2-78,8$15!$2-70,8$14!$2-68,8$13!$2-60,8#2!$2-58,8#3!$2-50,8$22!$2-48,8#43460!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000?0#800000000000&$2#10($2-?0#?0%#10000#<6<<0'$22#7???7?8000?0#7?????????>0&$22#8)$2-?0#?0$22##20($22##20'$25##??'&9$25#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 780464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_1ffdf7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 275516 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_1ffdf7.IT BndT_Ns_000.SegItab_Ns_1ffdf7.IT_sound BF NX0 BR XSTEP F0 PSS plan 275516 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsRzA.

End BndP_Ns_077.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_002 BndT_Ns_000.
Module BndP_Ns_078.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_002 BndT_Ns_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_078 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_ac3bb02ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB02BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB05XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB03kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078?LibSegNs_tsRzB23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_e530232ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078ALibSegNs_tsSub1_13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bc75132ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078@LibSegNs_tsSub2a3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_582f2f2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078BLibSegNs_tsSub2b_13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_4c7d4e2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW0S3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_ad16692ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1L3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_02b77c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW1S3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_c27f602ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_427ce82ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078=LibSegNs_tsW33kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_f5f21c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_078>LibSegNs_tsW4a3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_tsRzB0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_ac3bb0.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_ac3bb0.IT.
Definition ENDS : list Z := [761592].
Definition STOPS1 : list Z := [761592] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$22#8$29$;$<$=$>$?$10$11$24$26##2$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0%#10000#<6<<0'$22#7???7?8000<0#7?????????>0&$22#8)$2-<0#<0$22##20!$22#,1#1!$22#8,8#!$22#10,8#!$22#18,8#($22##20'$29#1000#7??????00000&$29#10($29##40,$29##40)$29##40$22##20)$2-<0#<0$29##40!$2-:8,8$26!$2-:0,8$24!$2-98,8#3!$2-90,8$22!$2-88,8#435=<!$2-78,8$15!$2-70,8$14!$2-68,8$13!$2-60,8#2!$2-58,8#3!$2-50,8$22!$2-48,8#43460!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28"%pstring).
Definition ss0 : sym_state := SS 276128 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 192); ((EVar 34), (0), ELit 32); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-192), 192); ((EVar 34), (0), 32); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9>?8#;9>?8#5=#;9>?8,20#$28$2$3$4$5$6$7$8$9+$29#10##8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$22#8,8#3!$29#8,8$26!$29#,8$24!$22#,1#1!$22#18,8$29!$22#10,8#8'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$22#7???7?8000<0#7?????????>0&$22#8)$2-<0#<0$22##20($22##20'$29#1000#7??????00000&$29#10($29##40,$29#10#30)$29##40$22##20)$2-<0#<0$29##40!$2-:8,8$26!$2-:0,8$24!$2-98,8#3!$2-90,8$22!$2-88,8#435=<!$2-78,8$15!$2-70,8$14!$2-68,8$13!$2-60,8#2!$2-58,8#3!$2-50,8$22!$2-48,8#43460!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761592 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_ac3bb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276128 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_ac3bb0.IT BndT_Ns_001.SegItab_Ns_ac3bb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 276128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsRzB0.

Module LibSegNs_tsRzB2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_ac3bb0.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_ac3bb0.IT.
Definition ENDS : list Z := [761592].
Definition STOPS1 : list Z := [761592] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$22#8$29$;$<$=$>$?$10$11$24$26#2#2$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0%#10000#<6<<0'$22#7???7?8000<0#7?????????>0&$22#8)$2-<0#<0$22##20!$22#,1#1!$22#8,8#!$22#10,8#!$22#18,8#($22##20'$29#1000#7??????00000&$29#10($29##40,$29##40)$29##40$22##20)$2-<0#<0$29##40!$2-:8,8$26!$2-:0,8$24!$2-98,8#3!$2-90,8$22!$2-88,8#435=<!$2-78,8$15!$2-70,8$14!$2-68,8$13!$2-60,8#2!$2-58,8#3!$2-50,8$22!$2-48,8#43460!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28"%pstring).
Definition ss0 : sym_state := SS 276128 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 192); ((EVar 34), (0), ELit 32); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-192), 192); ((EVar 34), (0), 32); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9>?8#;9>?8#5=#;9>?8,20#$28$2$3$4$5$6$7$8$9+$29#10##8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$22#8,8#3!$29#8,8$26!$29#,8$24!$22#,1#3!$22#18,8$29!$22#10,8#8'$2#7???7?8000<0#800000000000&$2#10($2-<0#<0'$22#7???7?8000<0#7?????????>0&$22#8)$2-<0#<0$22##20($22##20'$29#1000#7??????00000&$29#10($29##40,$29#10#30)$29##40$22##20)$2-<0#<0$29##40!$2-:8,8$26!$2-:0,8$24!$2-98,8#3!$2-90,8$22!$2-88,8#435=<!$2-78,8$15!$2-70,8$14!$2-68,8$13!$2-60,8#2!$2-58,8#3!$2-50,8$22!$2-48,8#43460!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761592 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_ac3bb0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276128 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_ac3bb0.IT BndT_Ns_001.SegItab_Ns_ac3bb0.IT_sound BF NX0 BR XSTEP F0 PSS plan 276128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsRzB2.

Module LibSegNs_tsSub1_0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_e53023.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_e53023.IT.
Definition ENDS : list Z := [277164].
Definition STOPS1 : list Z := [277164] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 33; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#150!$2-48,1$32'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2!$22#8,8#1!$22#10,8$24!$22#18,8#($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????"%pstring).
Definition ss0 : sym_state := SS 276616 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-336), ELit 336); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-336), 336); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22#2#1+$22#10+$22#10$24$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,34!$22#8,8#1!$22#18,8#!$2-148,8$15!$2-140,8$14!$2-138,8$13!$2-130,8#1!$2-128,8#2!$2-120,8$22!$2-118,8#43460!$2-?0,8+$2-38!$2->8,8#!$2->0,8$22!$2-=8,8#43=54!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8#!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#8,$2-110#20,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2!$22#10,8$24($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_e53023.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276616 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_e53023.IT BndT_Ns_002.SegItab_Ns_e53023.IT_sound BF NX0 BR XSTEP F0 PSS plan 276616 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsSub1_0.

Module LibSegNs_tsSub1_1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_e53023.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_e53023.IT.
Definition ENDS : list Z := [277164].
Definition STOPS1 : list Z := [277164] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 33; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#150!$2-48,1$32'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2!$22#8,8#1!$22#10,8$24!$22#18,8#($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#1!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????"%pstring).
Definition ss0 : sym_state := SS 276616 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-336), ELit 336); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-336), 336); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5;#43=;8,20##43=54+$2-=0$3$4$5$6$7$22#1#2+$22#18&4+$24$2:$24&4+$24$2:$24#+$24$2:$10$11+$2-30$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,34!$22#10,8+$24$2:!$22#18,8#!$22#8,8#2!$2-148,8$15!$2-140,8$14!$2-138,8$13!$2-130,8#1!$2-128,8#2!$2-120,8$22!$2-118,8#43460!$2-?0,8+$2-38!$2->8,8#1!$2->0,8$22!$2-=8,8#43=54!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#8,$2-110#20,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#1!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5;#43860,20##43=>8+$2-=0$3$4$5$6$7$22#1$22#2#1+$22#10+$22#10+$24$2:$10$11+$2-30$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,35!$22#8,8#1'&4&1&4+$24$2:$24##1#1#1!$22#10,8+$24$2:!$22#18,8#!$2-148,8$15!$2-140,8$14!$2-138,8$13!$2-130,8#1!$2-128,8#2!$2-120,8$22!$2-118,8#43460!$2-?0,8+$2-38!$2->8,8#1!$2->0,8$22!$2-=8,8#43=54!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#8,$2-110#20,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#1!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22##+$22#10+$22#8+$24$2:$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,36!$22#,1#!$22#8,8#'&4&1+$24$2:##1#1#1'&4&1&4+$24$2:$24##1#1#1!$22#10,8+$24$2:!$22#18,8#!$2-148,8$15!$2-140,8$14!$2-138,8$13!$2-130,8#1!$2-128,8#2!$2-120,8$22!$2-118,8#43460!$2-?0,8+$2-38!$2->8,8#1!$2->0,8$22!$2-=8,8#43=54!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#8,$2-110#20,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#1!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????,40!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22#2#1+$22#10+$22#10+$24$2:$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,36'&4&1+$24$2:##1##!$22#8,8#1'&4&1&4+$24$2:$24##1#1#1!$22#10,8+$24$2:!$22#18,8#!$2-148,8$15!$2-140,8$14!$2-138,8$13!$2-130,8#1!$2-128,8#2!$2-120,8$22!$2-118,8#43460!$2-?0,8+$2-38!$2->8,8#1!$2->0,8$22!$2-=8,8#43=54!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#8,$2-110#20,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#1!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22#2#2+$22#10+$22#18#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,35!$22#18,8#1'&4&1&4+$24$2:$24##1##!$22#10,8+$24$2:!$22#8,8#2!$2-148,8$15!$2-140,8$14!$2-138,8$13!$2-130,8#1!$2-128,8#2!$2-120,8$22!$2-118,8#43460!$2-?0,8+$2-38!$2->8,8#1!$2->0,8$22!$2-=8,8#43=54!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?800150#800000000000&$2#10($2-150#150%#10000#<6<<0,$2-150#8,$2-110#20,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?800150#7?????????>0&$22#8)$2-150#150$22##20!$22#,1#2($22##20'$24#1^#?#???????????????'$21#7???7?800150#7?????????>0&$21#8)$2-150#150$21##20!$21#,1#!$21#8,8#1!$21#10,8$2:!$21#18,8#)$21##20$22##20'$2:##????????,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_e53023.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276616 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_e53023.IT BndT_Ns_002.SegItab_Ns_e53023.IT_sound BF NX0 BR XSTEP F0 PSS plan 276616 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsSub1_1.

Module LibSegNs_tsSub2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bc7513.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bc7513.IT.
Definition ENDS : list Z := [275516].
Definition STOPS1 : list Z := [275516] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 33; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0%#10000#<6<<0,$2-=0#=0!$2-48,1$32'$32##??'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#2!$22#8,8#2!$22#10,8$24!$22#18,8$26($22##20'$21#7???7?8000=0#7?????????>0&$21#8)$2-=0#=0$21##20!$21#,1#!$21#8,8$29!$21#10,8$2:!$21#18,8#)$21##20$22##20'$29##1'$2:##????????"%pstring).
Definition ss0 : sym_state := SS 276616 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4343<#4343<#5=#4343<,20##43=54+$2-=0$3$4$5$6$7$22$29$22#3#1#1$>$?$10$11+$2-38$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$2-;0,8+$21#10!$2-:8,8$21!$2-:0,8$22!$2-98,8#438?<!$2-48,1&5@#4&6$32#2#2!$2-30,8#!$2-38,8$2:!$2-40,8$29!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0%#10000#<6<<0,$2-=0#20,$2-90#48,$2-47#7'$32##??'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#2!$22#8,8#2!$22#10,8$24!$22#18,8$26($22##20'$21#7???7?8000=0#7?????????>0&$21#8)$2-=0#=0$21##20!$21#,1#!$21#8,8$29!$21#10,8$2:!$21#18,8#)$21##20$22##20'$29##1'$2:##????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 275516 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bc7513.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276616 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bc7513.IT BndT_Ns_002.SegItab_Ns_bc7513.IT_sound BF NX0 BR XSTEP F0 PSS plan 276616 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsSub2a.

Module LibSegNs_tsSub2b_0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_582f2f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_582f2f.IT.
Definition ENDS : list Z := [277164].
Definition STOPS1 : list Z := [277164] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-=0$3$4$5$6$7$22#$:$;$<$=$>$?$10$11+$2-38$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0%#10000#<6<<0'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#3!$22#8,8#3!$22#10,8#8!$22#18,8$2;($22##20'$2;#1000#7??????00000&$2;#10($2;##40,$2;#18#28!$2;#,8$24!$2;#8,8$26!$2;#10,8#)$2;##40$22##20)$2-=0#=0$2;##40'$26#1^#4#'$2:##????????!$2-48,1$33'$33##??'&9$33#1##!$2-40,8#!$2-38,8$2:!$2-30,8#!$2-8,8$28!$2-10,8$8!$2-18,8$9!$2-20,8$12!$2-28,8$13!$2-98,8#438?<!$2-:0,8$22!$2-:8,8$21!$2-;0,8$34"%pstring).
Definition ss0 : sym_state := SS 277844 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EVar 34), (0), ELit 32); ((EVar 43), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EVar 34), (0), 32); ((EVar 43), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22#3#2$2;+$2;#8$26$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,26!$22#8,8#2'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0%#10000#<6<<0'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#3!$22#10,8#8!$22#18,8$2;($22##20'$2;#1000#7??????00000&$2;#10($2;##40,$2;#18#28!$2;#,8$24!$2;#8,8$26!$2;#10,8#)$2;##40$22##20)$2-=0#=0$2;##40'$26#1^#4#'$2:##????????!$2-48,1$33'$33##??'&9$33#1##!$2-40,8#!$2-38,8$2:!$2-30,8#!$2-8,8$28!$2-10,8$8!$2-18,8$9!$2-20,8$12!$2-28,8$13!$2-98,8#438?<!$2-:0,8$22!$2-:8,8$21!$2-;0,8$34,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_582f2f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277844 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_582f2f.IT BndT_Ns_001.SegItab_Ns_582f2f.IT_sound BF NX0 BR XSTEP F0 PSS plan 277844 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsSub2b_0.

Module LibSegNs_tsSub2b_1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_582f2f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_582f2f.IT.
Definition ENDS : list Z := [277164].
Definition STOPS1 : list Z := [277164] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-=0$3$4$5$6$7$22#1$:$;$<$=$>$?$10$11+$2-38$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0%#10000#<6<<0'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#3!$22#8,8#3!$22#10,8#8!$22#18,8$2;($22##20'$2;#1000#7??????00000&$2;#10($2;##40,$2;#18#28!$2;#,8$24!$2;#8,8$26!$2;#10,8#)$2;##40$22##20)$2-=0#=0$2;##40'$26#1^#4#'$2:##????????!$2-48,1$33'$33##??'&9$33#1##!$2-40,8#1!$2-38,8$2:!$2-30,8#!$2-8,8$28!$2-10,8$8!$2-18,8$9!$2-20,8$12!$2-28,8$13!$2-98,8#438?<!$2-:0,8$22!$2-:8,8$21!$2-;0,8$34"%pstring).
Definition ss0 : sym_state := SS 277844 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EVar 34), (0), ELit 32); ((EVar 43), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EVar 34), (0), 32); ((EVar 43), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5;#43=;8,20#$1+$2-=0$3$4$5$6$7$22#1#3+$2;#8&4+$24$2:$24&4+$24$2:$24#+$24$2:$10$11+$2-30$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,25!$2;#,8+$24$2:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#3!$22#8,8#3!$22#10,8#8!$22#18,8$2;($22##20'$2;#1000#7??????00000&$2;#10($2;##40,$2;#18#28!$2;#8,8$26!$2;#10,8#)$2;##40$22##20)$2-=0#=0$2;##40'$26#1^#4#'$2:##????????!$2-48,1$33'$33##??'&9$33#1##!$2-40,8#1!$2-38,8$2:!$2-30,8#!$2-8,8$28!$2-10,8$8!$2-18,8$9!$2-20,8$12!$2-28,8$13!$2-98,8#438?<!$2-:0,8$22!$2-:8,8$21!$2-;0,8$34,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22#3#2$2;+$2;#8$26$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,26!$22#8,8#2'&4&1&4+$24$2:$24##1#1#1!$2;#,8+$24$2:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#3!$22#10,8#8!$22#18,8$2;($22##20'$2;#1000#7??????00000&$2;#10($2;##40,$2;#18#28!$2;#8,8$26!$2;#10,8#)$2;##40$22##20)$2-=0#=0$2;##40'$26#1^#4#'$2:##????????!$2-48,1$33'$33##??'&9$33#1##!$2-40,8#1!$2-38,8$2:!$2-30,8#!$2-8,8$28!$2-10,8$8!$2-18,8$9!$2-20,8$12!$2-28,8$13!$2-98,8#438?<!$2-:0,8$22!$2-:8,8$21!$2-;0,8$34,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43::<#43::<#5=#43::<,20#$28$2$3$4$5$6$7$8$9$22#3#2$2;+$2;#8+$26#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,26!$22#8,8#2!$2;#8,8+$26#1'&4&1&4+$24$2:$24##1##!$2;#,8+$24$2:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$22#7???7?8000=0#7?????????>0&$22#8)$2-=0#=0$22##20!$22#,1#3!$22#10,8#8!$22#18,8$2;($22##20'$2;#1000#7??????00000&$2;#10($2;##40,$2;#18#28!$2;#10,8#)$2;##40$22##20)$2-=0#=0$2;##40'$26#1^#4#'$2:##????????!$2-48,1$33'$33##??'&9$33#1##!$2-40,8#1!$2-38,8$2:!$2-30,8#!$2-8,8$28!$2-10,8$8!$2-18,8$9!$2-20,8$12!$2-28,8$13!$2-98,8#438?<!$2-:0,8$22!$2-:8,8$21!$2-;0,8$34,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 277164 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_582f2f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277844 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_582f2f.IT BndT_Ns_001.SegItab_Ns_582f2f.IT_sound BF NX0 BR XSTEP F0 PSS plan 277844 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsSub2b_1.

Module LibSegNs_tsW0L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4c7d4e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4c7d4e.IT.
Definition ENDS : list Z := [290440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:"%pstring).
Definition ss0 : sym_state := SS 289856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672); ((EVar 45), (0), ELit 24); ((EVar 47), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672); ((EVar 45), (0), 24); ((EVar 47), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46>88#5=#46>88,20#$28$2$3$4$5$6$7$8$9##1$31&9$25#2$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3<!$2?#1,1#!$2?#,1#30!$2=#8,8#1!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=;4!$2-60,8$26!$2-68,8$24!$2-70,8#!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#48,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#2#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4c7d4e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4c7d4e.IT BndT_Ns_000.SegItab_Ns_4c7d4e.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW0L.

Module LibSegNs_tsW0S.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4c7d4e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4c7d4e.IT.
Definition ENDS : list Z := [290440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##"%pstring).
Definition ss0 : sym_state := SS 289856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672); ((EVar 45), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672); ((EVar 45), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46>88#5=#46>88,20#$28$2$3$4$5$6$7$8$9##30#2&9$25#2$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,32!$2=#2,1#!$2=#1,1#30!$2=#,1#2!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=;4!$2-60,8$26!$2-68,8$24!$2-70,8#!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1:0,$2-<0#48,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'&9$31#1##'&9$31#??##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4c7d4e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4c7d4e.IT BndT_Ns_000.SegItab_Ns_4c7d4e.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW0S.

Module LibSegNs_tsW1L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_ad1669.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_ad1669.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:"%pstring).
Definition ss0 : sym_state := SS 289856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,3<!$2-:0,8#!$2-:8,8^#8#:<7230489>80000!$2-;0,8#1!$2-;8,1#!$2-80,8#!$2-88,8#!$2-90,8#!$2-98,1#!$2-60,8$26!$2-68,8$24!$2-70,8#1!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1>8,$2-;7#7,$2-97#7,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_ad1669.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_ad1669.IT BndT_Ns_001.SegItab_Ns_ad1669.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW1L.

Module LibSegNs_tsW1S.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_02b77c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_02b77c.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##"%pstring).
Definition ss0 : sym_state := SS 289856 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#;>8;0#5=#;>8;0,20##660>0+$2-110$3$4$5$6$7$2=#19#1:@#100000000000000$31##16$>$?$10$11#1#1:&6@#100000000000000$31#39#16#+@#2&6$31#1-1$18$19$1:$1;$1<$1=$1>$1?,,32!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#1!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<:8!$2-60,8$26!$2-68,8$24!$2-70,8#1!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#198,$2-<0#48,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 780464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_02b77c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_02b77c.IT BndT_Ns_000.SegItab_Ns_02b77c.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW1S.

Module LibSegNs_tsW2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_c27f60.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_c27f60.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#19$30$;$<$=$>$?$10$11$12#1:##16#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18'$30#1000#7??????00000"%pstring).
Definition ss0 : sym_state := SS 418016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#;9=7<#5=#;9=7<,20##66160+$2-110$3$4$5$6$7$2=#19$30+$2=#1#1$=$>$?$10$11$30+$2=#1##16#$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18'$30#1000#7??????00000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_c27f60.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_c27f60.IT BndT_Ns_002.SegItab_Ns_c27f60.IT_sound BF NX0 BR XSTEP F0 PSS plan 418016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW2.

Module LibSegNs_tsW3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_427ce8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_427ce8.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#19$:$;$<$=$>$?$10$11$30+$2=#1##16#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18'$30#1000#7??????00000!$2-<8,8#46<:8!$2-=0,8$2=!$2-=8,8$22!$2->0,8#1!$2->8,8$46!$2-?0,8$47!$2-?8,8$48!$2-100,8$49!$2-108,8$4:"%pstring).
Definition ss0 : sym_state := SS 418144 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 2), (-184), ELit 64); ((EVar 45), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 2), (-184), 64); ((EVar 45), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$49$4:$18$19$1:$1;$1<$1=$1>$1?,,21!$2-:0,8#!$2-:8,8^#8#:<7230489>80000!$2-;0,8#1!$2-;8,1#!$2-80,8#!$2-88,8#!$2-90,8#!$2-98,1#!$2=#10,8$30!$2=#8,8#!$2=#,8#1;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1>8,$2-;7#7,$2-97#7,$2-78#78'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18'$30#1000#7??????00000!$2-<8,8#46<:8!$2-=0,8$2=!$2-=8,8$22!$2->0,8#1!$2->8,8$46!$2-?0,8$47!$2-?8,8$48!$2-100,8$49!$2-108,8$4:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_427ce8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418144 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_427ce8.IT BndT_Ns_000.SegItab_Ns_427ce8.IT_sound BF NX0 BR XSTEP F0 PSS plan 418144 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW3.

Module LibSegNs_tsW4a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290104].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#1!$2-98,1$3:'$3:##??'&9$3:#1##!$2-88,8$2<!$2-70,8$34'$34##1"%pstring).
Definition ss0 : sym_state := SS 290052 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46=38#5=#46=38,20#$1+$2-<0$3$4$5$6$7$2=$22##$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$2<$34@-1$34$19$1:$1;$1<$1=$1>$1?,,1<'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#1!$2-98,1$3:'$3:##??'&9$3:#1##!$2-88,8$2<!$2-70,8$34'$34##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290052 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290052 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW4a.

End BndP_Ns_078.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000.
Module BndP_Ns_076.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_076 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_18bef92ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qE3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12qI3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12tS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12uS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076?LibSegNs_ts12vS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8a03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076>LibSegNs_ts8cS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_076=LibSegNs_ts8d3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ts12qE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [286912].
Definition STOPS1 : list Z := [286912] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>"%pstring).
Definition ss0 : sym_state := SS 287148 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#460<0#460<0#5=#460<0,20#$28$2$3$4$5$6$7$29$2:$:$;$<$=$>$?$10$11$2;$2<$2=$2>$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 286912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287148 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287148 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12qE.

Module LibSegNs_ts12qI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [286912].
Definition STOPS1 : list Z := [286912] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$24#10,1#!$2-68,1$21'$21##??'&9$21#1##"%pstring).
Definition ss0 : sym_state := SS 287288 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#460<0#460<0#5=#460<0,20#$28$2$3$4$5$6$7$29$2:#1#$<$=$>$?$10$11$2;$2<$2=$2>$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#8,1#1'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$24#10,1#!$2-68,1$21'$21##??'&9$21#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 286912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287288 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287288 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12qI.

Module LibSegNs_ts12tL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [289856].
Definition STOPS1 : list Z := [289856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1#1#1!$24#158,8$27'$27#1000#7???????0000($27##1($24#148#18)$27##1$24##190)$2-90#90$27##1)$27##1$25##60)$27##1$26##10!$2-90,1#"%pstring).
Definition ss0 : sym_state := SS 286828 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (336), ELit 8); ((EVar 39), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (336), 8); ((EVar 39), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46<40#46<40#5=#46<40,20##461>8+$2-90$3$4$5$6$7$24$26+$2-68+$24#148$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$24#150,8#!$27#,1#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1#1#1!$24#158,8$27'$27#1000#7???????0000($27##1($24#148#18)$27##1$24##190)$2-90#90$27##1)$27##1$25##60)$27##1$26##10!$2-90,1#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286828 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286828 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12tL.

Module LibSegNs_ts12tS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [289856].
Definition STOPS1 : list Z := [289856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1##($24#148#18!$2-90,1#"%pstring).
Definition ss0 : sym_state := SS 286828 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (328), ELit 2)].
Definition F0L : list SR.region := [((EVar 36), (328), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46<40#46<40#5=#46<40,20##461>8+$2-90$3$4$5$6$7$24$26+$2-68+$24#148$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#148,2#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$21##??'&9$21#1##($24#148#18!$2-90,1#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286828 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286828 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12tS.

Module LibSegNs_ts12uL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [289856].
Definition STOPS1 : list Z := [289856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1#1#1!$24#158,8$27'$27#1000#7???????0000($27##1($24#148#18)$27##1$24##190)$2-90#90$27##1)$27##1$25##60)$27##1$26##10"%pstring).
Definition ss0 : sym_state := SS 287164 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (336), ELit 8); ((EVar 39), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (336), 8); ((EVar 39), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46<40#46<40#5=#46<40,20##461>8+$2-90$3$4$5$6$7$24$26+$2-68+$24#148$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#150,8#!$27#,1#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1#1#1!$24#158,8$27'$27#1000#7???????0000($27##1($24#148#18)$27##1$24##190)$2-90#90$27##1)$27##1$25##60)$27##1$26##10,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287164 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287164 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12uL.

Module LibSegNs_ts12uS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [289856].
Definition STOPS1 : list Z := [289856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1##($24#148#18"%pstring).
Definition ss0 : sym_state := SS 287164 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (328), ELit 2)].
Definition F0L : list SR.region := [((EVar 36), (328), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46<40#46<40#5=#46<40,20##461>8+$2-90$3$4$5$6$7$24$26+$2-68+$24#148$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$24#148,2#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$21##??'&9$21#1##($24#148#18,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287164 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287164 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12uS.

Module LibSegNs_ts12vL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [244020].
Definition STOPS1 : list Z := [244020] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1#1#1!$24#150,8$28!$24#158,8$27"%pstring).
Definition ss0 : sym_state := SS 287208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-144), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;934#3;934#5=#3;934,20##46238+$2-90$3$4$5$6$7$24$26$25+$2-90#7$24$26#3;934$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$2-88,8$28!$2-90,8$27'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1#1#1!$24#150,8$28!$24#158,8$27,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 244020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12vL.

Module LibSegNs_ts12vS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [244020].
Definition STOPS1 : list Z := [244020] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1##"%pstring).
Definition ss0 : sym_state := SS 287208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-144), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;934#3;934#5=#3;934,20##46238+$2-90$3$4$5$6$7$24$26$25+$2-90#7$24$26#3;934$10$11$25$37$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$2-88,8&6$21#1!$2-90,8+$24#149'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 244020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts12vS.

Module LibSegNs_ts8a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [279660].
Definition STOPS1 : list Z := [279660] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1"%pstring).
Definition ss0 : sym_state := SS 285744 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-104), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-104), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4446<#4446<#5=#4446<,20##45<5<+$2-90$3$4$5$6$7$24$26+$2-68#3;9:<:00$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-50,8#!$2-58,8&6@#40000000$23#1>!$2-60,8&4#&6@#40000000$23#1>!$2-68,1#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 279660 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 285744 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 285744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8a.

Module LibSegNs_ts8a0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [285744].
Definition STOPS1 : list Z := [285744] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$31$;$<$=$>$?$10$11$25+$24#18#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$31#8#8,$2-48#8"%pstring).
Definition ss0 : sym_state := SS 285636 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#45<30#45<30#5=#45<30,20#$1+$2-90$3$4$5$6$7$24$26&8+@#100000000000000$40@#10000000000&9$40#??00&8@#1000000&9$40#??0000@#100000000%6$40#18@#10000000000&9$40#??00&8@#1000000&9$40#??0000@#100000000%6$40#18&8+&9&6$40#18#??0000@#1000000%6&6$40#8#18&8&9&6$40#28#??00&6$40#38+&9&6$40#18#??0000@#1000000%6&6$40#8#18&9&6$40#18#??0000$10$11$25&8&8+@#100000000000000$40@#10000000000&9$40#??00&8@#1000000&9$40#??0000@#100000000%6$40#18&8+&9&6$40#18#??0000@#1000000%6&6$40#8#18&8&9&6$40#28#??00&6$40#38#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$31#8#8,$2-48#8,41!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 285744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 285636 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 285636 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8a0.

Module LibSegNs_ts8b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [274952].
Definition STOPS1 : list Z := [274952] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$23$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1"%pstring).
Definition ss0 : sym_state := SS 285788 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43208#43208#5=#43208,20##45<68+$2-90$3$4$5$6$7$24$26+$2-68&6$23#22$<$=$>$?$10$11$25$23$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 285788 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 285788 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8b.

Module LibSegNs_ts8cL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [289856].
Definition STOPS1 : list Z := [289856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1#1#1!$24#158,8$27'$27#1000#7???????0000($27##1($24#148#18)$27##1$24##190)$2-90#90$27##1)$27##1$25##60)$27##1$26##10"%pstring).
Definition ss0 : sym_state := SS 285800 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (336), ELit 8); ((EVar 39), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (336), 8); ((EVar 39), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46<40#46<40#5=#46<40,20##46130+$2-90$3$4$5$6$7$24$26+$2-68+$24#148$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#150,8#!$27#,1#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1#1#1!$24#158,8$27'$27#1000#7???????0000($27##1($24#148#18)$27##1$24##190)$2-90#90$27##1)$27##1$25##60)$27##1$26##10,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 285800 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 285800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8cL.

Module LibSegNs_ts8cS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [289856].
Definition STOPS1 : list Z := [289856] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$24#148,1$21'$21##??'&9$21#1##($24#148#18"%pstring).
Definition ss0 : sym_state := SS 285800 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (328), ELit 2)].
Definition F0L : list SR.region := [((EVar 36), (328), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46<40#46<40#5=#46<40,20##46130+$2-90$3$4$5$6$7$24$26+$2-68+$24#148$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$24#148,2#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1'$21##??'&9$21#1##($24#148#18,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289856 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 285800 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 285800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8cS.

Module LibSegNs_ts8d.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [244020].
Definition STOPS1 : list Z := [244020] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1#1#1!$24#150,8$28!$24#158,8$27"%pstring).
Definition ss0 : sym_state := SS 287024 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-144), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;934#3;934#5=#3;934,20##46180+$2-90$3$4$5$6$7$24$26$25+$2-90#7$24$26#3;934$10$11$25$23#8#??$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$2-88,8$28!$2-90,8$27'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$25#,8#;?:88!$24#148,1$21'$21##??'&9$21#1#1#1!$24#150,8$28!$24#158,8$27,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 244020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts8d.

End BndP_Ns_076.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_000.
Module BndP_Ns_079.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_079 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_f5f21c2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW4b3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_effcfe2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6aB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsW6b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsW6bB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWr13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079?LibSegNs_tsWr1C3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_tsWsg3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tsWt3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_18bef92ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q92BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q92BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q95XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q94planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079>LibSegNs_ts_q93kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_c27f602ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_079=LibSegNs_tw2S3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_tsW4b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290104].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-70,8$34'$34##1"%pstring).
Definition ss0 : sym_state := SS 290052 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46=38#5=#46=38,20#$1+$2-<0$3$4$5$6$7$2=$22#$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12#$34@-1$34$19$1:$1;$1<$1=$1>$1?,,1;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-70,8$34'$34##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290052 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290052 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW4b.

Module LibSegNs_tsW6A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290136].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$36$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$33$3;$3<$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12"%pstring).
Definition ss0 : sym_state := SS 290104 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46=58#5=#46=58,20#$1+$2-<0$3$4$5$6$7$2=$22+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3$3;$3<$36$1:$1;$1<$1=$1>$1?,,29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290136 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW6A.

Module LibSegNs_tsW6a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 290160].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$36$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$33##$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12"%pstring).
Definition ss0 : sym_state := SS 290104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,34!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,35'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1#1#1!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,35'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,36'&4$36#12#1#1'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,36'&4$36#12##'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW6a.

Module LibSegNs_tsW6aB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 290160].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$38$37$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999"%pstring).
Definition ss0 : sym_state := SS 290136 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,36!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,37'&4&1$3=##1#1#1!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,37'&4&1$3=##1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,38'&4$36#12#1#1'&4&1$3=##1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,38'&4$36#12##'&4&1$3=##1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290136 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290136 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW6aB.

Module LibSegNs_tsW6b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 271440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$36$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$33#1-1$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12"%pstring).
Definition ss0 : sym_state := SS 290104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,34!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,35'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1#1#1!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,35'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,36'&4$36#12#1#1'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,36'&4$36#12##'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW6b.

Module LibSegNs_tsW6bB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 271440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$38$37$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39"%pstring).
Definition ss0 : sym_state := SS 290136 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,35!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,36'&4&1$3=-1#1#1#1!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,36'&4&1$3=-1#1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,37'&4$36#12#1#1'&4&1$3=-1#1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,37'&4$36#12##'&4&1$3=-1#1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290136 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290136 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsW6bB.

Module LibSegNs_tsWr0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290264; 290296].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35#1#15"%pstring).
Definition ss0 : sym_state := SS 290184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5;#46==0,20#$1+$2-<0$3$4$5$6$7$2=$22$2?++$2?$35-1#1$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,24'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35#1#15,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5=#46==8,20#$1+$2-<0$3$4$5$6$7$2=$22+$2?#1++$2?$35-1#1$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,25'&4$2?++$2?$35-1#1#1'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35#1#15,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5=#46=?8,20#$1+$2-<0$3$4$5$6$7$2=$22$2?++$2?$35-1#1$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,25'&4$2?++$2?$35-1##'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35#1#15,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsWr0.

Module LibSegNs_tsWr1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290264; 290296].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$37$38$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000,$38##1($38##1,$37-1#1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1"%pstring).
Definition ss0 : sym_state := SS 290264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 55), (-1), ELit 1); ((EVar 56), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 55), (-1), 1); ((EVar 56), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=?4,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$51$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$38#,1$51!$37-1,1$50'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1##'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1,52!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5=#46==8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$51$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4$37+$38-1#1#1!$38#,1$51!$37-1,1$50'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1##'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1,52!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5=#46=?8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$51$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4$37+$38-1##!$38#,1$51!$37-1,1$50'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1##'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1,52!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290264 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsWr1.

Module LibSegNs_tsWr1C.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290264; 290296].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$37$38$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000,$38##1($38##1,$37-1#1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1!$37-1,1$39'$39##??!$38#,1$3:'$3:##??"%pstring).
Definition ss0 : sym_state := SS 290264 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 55), (-1), ELit 1); ((EVar 56), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 55), (-1), 1); ((EVar 56), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=?4,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$39$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$38#,1$39!$37-1,1$3:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1##'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1'$39##??'$3:##??,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5=#46==8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$39$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4$37+$38-1#1#1!$38#,1$39!$37-1,1$3:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1##'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1'$39##??'$3:##??,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#42450#;9=7<#46==8#46=?8#5=#46=?8,20#$1+$2-<0$3$4$5$6$7$2=$22+$37#1+$38-1$37$39$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4$37+$38-1##!$38#,1$39!$37-1,1$3:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1##'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18'$37#1000#7??????00000'$38#1000#7??????00000($38##1($37-1#1)$37-1#1$38##1)$2-2:0#2:0$37-1#1)$2-2:0#2:0$38##1'$39##??'$3:##??,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290296 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290264 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsWr1C.

Module LibSegNs_tsWsg.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290184].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20"%pstring).
Definition ss0 : sym_state := SS 290160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46=88#5;#46=78,20#$1+$2-<0$3$4$5$6$7$2=$22&9$25#2$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46=88#5=#46=88,20#$1+$2-<0$3$4$5$6$7$2=$22&9$25#2$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,29'&4&1&9$25#2##1#1#1'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46=88#5=#46=88,20##46=88+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,34!+$2?$35#1,1#!+$2?$35#,1#2=!$2=#8,8+$35#1!$2-100,8$16!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=88'&4&1&9$25#2##1##'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#1!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#1;#10000001'+&9$2>-2-1#19#???????'$2?#1000#7??????00000($2?##1:,$2?#$35,+$2?$35#2+@-1$35#18)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:'$35##14(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PEnd 1))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SR.PS 290184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 290184 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsWsg.

Module LibSegNs_tsWt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290440].
Definition STOPS1 : list Z := [290440; 780464; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0!$2-;8,1#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-78,1$39'$39##??'&9$39#1##!$2-8,8$28!$2-10,8$40!$2-18,8$41!$2-20,8$42!$2-28,8$43!$2-30,8$44!$2-38,8$45!$2-40,8$46!$2-48,8$47!$2-50,8$48!$2-58,8$49"%pstring).
Definition ss0 : sym_state := SS 290296 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#46>88#;>8;0#42450#;9=7<#46>88#5=#46>88,20#$28$2$3$4$5$6$7$40$41#$;$<$=$>$?$10$11$42$43$44$45$46$47$48$49$1:$1;$1<$1=$1>$1?,,16'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0!$2-;8,1#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-78,1$39'$39##??'&9$39#1##!$2-8,8$28!$2-10,8$40!$2-18,8$41!$2-20,8$42!$2-28,8$43!$2-30,8$44!$2-38,8$45!$2-40,8$46!$2-48,8$47!$2-50,8$48!$2-58,8$49,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290296 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290296 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tsWt.

Module LibSegNs_ts_q9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [286912].
Definition STOPS1 : list Z := [286912] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$24#10,1#!$2-68,1$21'$21##??'&9$21#1##"%pstring).
Definition ss0 : sym_state := SS 287104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1)].
Definition F0L : list SR.region := [((EVar 36), (8), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#460<0#460<0#5=#460<0,20#$28$2$3$4$5$6$7$29$2:#1#$<$=$>$?$10$11$2;$2<$2=$2>$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#8,1#1'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$24#10,1#!$2-68,1$21'$21##??'&9$21#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 286912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 287104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ts_q9.

Module LibSegNs_tw2M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_c27f60.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_c27f60.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#2?$30$;$<$=$>$?$10$11$12#30#$4;#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18!$2=#8,8#!$2=#10,8$2?'$2?#1000#7??????00000'$30#1000#7??????00000"%pstring).
Definition ss0 : sym_state := SS 418016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;9=7<#5=#;9=7<,20##66160+$2-110$3$4$5$6$7$2=#2?$30$2?#1$=$>$?$10$11$30$2?#$4;#1$17$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18!$2=#8,8#!$2=#10,8$2?'$2?#1000#7??????00000'$30#1000#7??????00000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_c27f60.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_c27f60.IT BndT_Ns_002.SegItab_Ns_c27f60.IT_sound BF NX0 BR XSTEP F0 PSS plan 418016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw2M.

Module LibSegNs_tw2S.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_c27f60.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_c27f60.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#2?$30$;$<$=$>$?$10$11$12#30##16#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18'$30#1000#7??????00000"%pstring).
Definition ss0 : sym_state := SS 418016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;9=7<#5=#;9=7<,20##66160+$2-110$3$4$5$6$7$2=#2?$30+$2=#1#1$=$>$?$10$11$30+$2=#1##16#$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18'$30#1000#7??????00000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_c27f60.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_c27f60.IT BndT_Ns_002.SegItab_Ns_c27f60.IT_sound BF NX0 BR XSTEP F0 PSS plan 418016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw2S.

End BndP_Ns_079.
Module BndP_Ns_080.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_000 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_080 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_c27f602ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3M3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_427ce82ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw3S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4M3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_f5f21c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw4b3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_effcfe2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6aB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_tw6b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_tw6bB3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_2362cb2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2a3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_19bd262ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2b3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_a8b1082ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080>LibSegNs_twD2c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0163;BndP_Ns_080=LibSegNs_twDa3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_tw3M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_c27f60.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_c27f60.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#2?$:$;$<$=$>$?$10$11$30$2?#$4;#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18'$2?#1000#7??????00000'$30#1000#7??????00000'$4;#19#2;"%pstring).
Definition ss0 : sym_state := SS 418144 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#63=<4#5=#63=<4,20##66190+$2-110$3$4$5$6$7$2=#2?$2?+$4;#1$<$=$>$?$10$11$30$2?#$4;#1$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18'$2?#1000#7??????00000'$30#1000#7??????00000'$4;#19#2;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 409028 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_c27f60.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418144 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_c27f60.IT BndT_Ns_002.SegItab_Ns_c27f60.IT_sound BF NX0 BR XSTEP F0 PSS plan 418144 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw3M.

Module LibSegNs_tw3S.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_427ce8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_427ce8.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#2?$:$;$<$=$>$?$10$11$30+$2=#1##16#$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18'$30#1000#7??????00000!$2-<8,8#46<:8!$2-=0,8$2=!$2-=8,8$22!$2->0,8#2!$2->8,8$46!$2-?0,8$47!$2-?8,8$48!$2-100,8$49!$2-108,8$4:"%pstring).
Definition ss0 : sym_state := SS 418144 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 2), (-184), ELit 64); ((EVar 45), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 2), (-184), 64); ((EVar 45), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$49$4:$18$19$1:$1;$1<$1=$1>$1?,,21!$2-:0,8#!$2-:8,8^#8#:<7230489>80000!$2-;0,8#1!$2-;8,1#!$2-80,8#!$2-88,8#!$2-90,8#!$2-98,1#!$2=#10,8$30!$2=#8,8#!$2=#,8#31'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1>8,$2-;7#7,$2-97#7,$2-78#78'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18'$30#1000#7??????00000!$2-<8,8#46<:8!$2-=0,8$2=!$2-=8,8$22!$2->0,8#2!$2->8,8$46!$2-?0,8$47!$2-?8,8$48!$2-100,8$49!$2-108,8$4:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_427ce8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418144 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_427ce8.IT BndT_Ns_000.SegItab_Ns_427ce8.IT_sound BF NX0 BR XSTEP F0 PSS plan 418144 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw3S.

Module LibSegNs_tw4M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_427ce8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_427ce8.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-110$3$4$5$6$7$2=#2?$:$;$<$=$>$?$10$11$30$13#$15#1$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18'$30#1000#7??????00000!$2-<8,8#46<:8!$2-=0,8$2=!$2-=8,8$22!$2->0,8#2!$2->8,8$46!$2-?0,8$47!$2-?8,8$48!$2-100,8$49!$2-108,8$4:"%pstring).
Definition ss0 : sym_state := SS 418192 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 2), (-184), ELit 64); ((EVar 45), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 2), (-184), 64); ((EVar 45), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$49$4:$18$19$1:$1;$1<$1=$1>$1?,,21!$2-:0,8#!$2-:8,8^#8#:<7230489>80000!$2-;0,8#1!$2-;8,1#!$2-80,8#!$2-88,8#!$2-90,8#!$2-98,1#!$2=#10,8$30!$2=#8,8#!$2=#,8#31'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1>8,$2-;7#7,$2-97#7,$2-78#78'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18'$30#1000#7??????00000!$2-<8,8#46<:8!$2-=0,8$2=!$2-=8,8$22!$2->0,8#2!$2->8,8$46!$2-?0,8$47!$2-?8,8$48!$2-100,8$49!$2-108,8$4:,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_427ce8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418192 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_427ce8.IT BndT_Ns_000.SegItab_Ns_427ce8.IT_sound BF NX0 BR XSTEP F0 PSS plan 418192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw4M.

Module LibSegNs_tw4a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290104].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#1!$2-98,1$3:'$3:##??'&9$3:#1##!$2-88,8$2<!$2-70,8$34'$34##1"%pstring).
Definition ss0 : sym_state := SS 290052 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46=38#5=#46=38,20#$1+$2-<0$3$4$5$6$7$2=$22##$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$2<$34@-1$34$19$1:$1;$1<$1=$1>$1?,,16'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#1!$2-98,1$3:'$3:##??'&9$3:#1##!$2-88,8$2<!$2-70,8$34'$34##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290052 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290052 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw4a.

Module LibSegNs_tw4b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_f5f21c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_f5f21c.IT.
Definition ENDS : list Z := [290104].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$:$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-70,8$34'$34##1"%pstring).
Definition ss0 : sym_state := SS 290052 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46=38#5=#46=38,20#$1+$2-<0$3$4$5$6$7$2=$22#$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12#$34@-1$34$19$1:$1;$1<$1=$1>$1?,,15'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-90,8#!$2-98,1$3:'$3:##??'&9$3:#1##!$2-70,8$34'$34##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_f5f21c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290052 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_f5f21c.IT BndT_Ns_002.SegItab_Ns_f5f21c.IT_sound BF NX0 BR XSTEP F0 PSS plan 290052 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw4b.

Module LibSegNs_tw6A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290136].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$36$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$33$3;$3<$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12"%pstring).
Definition ss0 : sym_state := SS 290104 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#46=58#5=#46=58,20#$1+$2-<0$3$4$5$6$7$2=$22+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3$3;$3<$36$1:$1;$1<$1=$1>$1?,,23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 290136 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw6A.

Module LibSegNs_tw6a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 290160].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$36$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$33##$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12"%pstring).
Definition ss0 : sym_state := SS 290104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,2>!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,2?'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1#1#1!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,2?'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,30'&4$36#12#1#1'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3##$36$1:$1;$1<$1=$1>$1?,,30'&4$36#12##'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3##1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw6a.

Module LibSegNs_tw6aB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 290160].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$38$37$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",25'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999"%pstring).
Definition ss0 : sym_state := SS 290136 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,30!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,31'&4&1$3=##1#1#1!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,31'&4&1$3=##1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,32'&4$36#12#1#1'&4&1$3=##1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#46=70#5=#46=70,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=##$36$1:$1;$1<$1=$1>$1?,,32'&4$36#12##'&4&1$3=##1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##1>(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39'$3=#^#1#999999999999999,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 290160 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290136 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290136 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw6aB.

Module LibSegNs_tw6b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 271440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$36$;$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$33#1-1$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12"%pstring).
Definition ss0 : sym_state := SS 290104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,2>!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,2?'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1#1#1!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,2?'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,30'&4$36#12#1#1'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12&6/3$33^#<#<<<<<<<<<<<<<<=#3#1-1$36$1:$1;$1<$1=$1>$1?,,30'&4$36#12##'&4&1&6/3$33^#<#<<<<<<<<<<<<<<=#3-1#1##!+$2?$35#1,1#!+$2?$35#,1&9+&9%1$33@#:&6/3$33^#<#<<<<<<<<<<<<<<=#3-31#30#??!$2=#8,8+$35#1!$2-100,8&6/3$33^#<#<<<<<<<<<<<<<<=#3!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw6b.

Module LibSegNs_tw6bB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_effcfe.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_effcfe.IT.
Definition ENDS : list Z := [290104; 271440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$2=$22$38$37$<$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8$35!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39"%pstring).
Definition ss0 : sym_state := SS 290136 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 480); ((EVar 45), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-672), 480); ((EVar 45), (0), 24); ((EAlu Instr.ALU_ADD (EVar 47) (EVar 53)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#46=60,20##46=60+$2-<0$3$4$5$6$7$2=$22+$2?$35+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,2?!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,30'&4&1$3=-1#1#1#1!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5;#46=68,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,30'&4&1$3=-1#1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5=#46=38,20##46=60+$2-<0$3$4$5$6$7$2=$22+$36#1+$35#1$31$=$>$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,31'&4$36#12#1#1'&4&1$3=-1#1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,7#46>88#;>8;0#63=<4#42450#;9=7<#46=38#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$3=#1-1$36$1:$1;$1<$1=$1>$1?,,31'&4$36#12##'&4&1$3=-1#1##!+$2?$35#1,1#!+$2?$35#,1$37!$2=#8,8+$35#1!$2-100,8$3=!$2-?8,8#12!$2-?0,8^#<#<<<<<<<<<<<<<<=!$2->8,8#:!$2->0,8+$2-88!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46=60'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0,$2-2:0#1:0,$2-<0#<0'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?#$35,+$2?$35#2+@-1$35#1>)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20'$35##12(+$2?$35##2)+$2?$35##2$2=##18)$2-2:0#2:0+$2?$35##2)+$2?$35##2$22##20'$36##12'$37#30#39,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 0)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s6).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s6).
Definition ps0 : SR.post_spec := SR.PS 290104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 271440 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_effcfe.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 290136 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_effcfe.IT BndT_Ns_002.SegItab_Ns_effcfe.IT_sound BF NX0 BR XSTEP F0 PSS plan 290136 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tw6bB.

Module LibSegNs_twD2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2362cb.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2362cb.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8$39!$2#38,8$2<!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8#8!$2#60,8$29'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40!$29#,8$24!$29#8,8$26,$29#10#30!$2-88,1$32'$32##??!$2-:8,1$33'$33##??!$2-<8,1$34'$34##??!$2->8,1$35'$35##??'$24#1#7???????'$39##1"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#;>8;0#5=#;>8;0,20##43;?<+$2-170$3$4$5$6$7+$2#48+$2-:8#40#+$2-<8#1#1$?$10$11#1#1+$2-78+$2-78$25#1$18$19$1:+$2#28$1<$1=$1>$1?,,41!$2-90,8#!$2-98,8#8!$2-:0,8#1!$2-:8,1&8&9$25#2&9+@#2&6$33#1#1#?=!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8@#4&6$32#2!$2-138,8#424=8!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-88,1@#4&6$32#2!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#90,$2-130#88,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8$39!$2#38,8$2<!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8#8!$2#60,8$29'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$32##??'$33##??!$2-<8,1$34'$34##??!$2->8,1$35'$35##??'$24#1#7???????'$39##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 780464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2362cb.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2362cb.IT BndT_Ns_000.SegItab_Ns_2362cb.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twD2a.

Module LibSegNs_twD2b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_19bd26.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_19bd26.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-170$3$4$<=$<>$<?+$2#48+$2-:8$2:$=3$=4$=5$=6$=7$=8$=9#1#1+$2-78+$2-78$25#1$18$19$1:+$2#28$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",4:'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$24#1#7???????'$39##1!$2-90,8#!$2-98,8#8!$2-:0,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8@#4&6$32#2!$2-138,8#424=8!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-88,1@#4&6$32#2!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-170#20,$2-130#88,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8$39!$2#38,8$2<!$2#40,8#!$2#48,1$25!$2#50,8#1!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2-<8,1$34!$2->8,1$35!$2-:8,1$37,$2-1>0#70'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40,$2:##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1"%pstring).
Definition ss0 : sym_state := SS 277500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96); ((EVar 42), (0), ELit 64); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96); ((EVar 42), (0), 64); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,5#42:18#44000#;>8;0#63=<4#63=<4!#!!,5#42:18#44000#;>8;0#63=<4#63=<4#5;#43464,20##43460+$2-1:0$3$4$?<$?=$?>+$2#28#1$2;##2#1$24^#8#:<7230489>80000+$2-80@#4&6$32#2$39+$2-:8&9$37#?=+$2-78$25#1$18$19&9$25#2+$2#28$107$108$109$10:,,5<!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8$39!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42580!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2-90,8$2:'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$24#1#7???????'$39##1!$2-98,8#8!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#38,8$2<!$2#40,8#!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2-1>0#8,$2-1:0#20'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40,$2:#8#38)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1,10;!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ce2 : expr := EVar 57.
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,5#42:18#44000#;>8;0#63=<4#63=<4!#!!,5#42:18#44000#;>8;0#63=<4#63=<4#5=#63=<4,20##429<0+$2-130$3$4$10<$10=$10>&6&5#&9$25#2#1+$2#48$2:#40$111$112$113$114$115$116+$2#48#1+$2-78+$2-78$25#1$18$19&9$25#2+$2#28$117$118$119$11:,,5=!$2#28,1&8&9$2;#?=&9$25#2!$2#38,8$24!$2#40,8#'$39##!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8$39!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42580!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2-90,8$2:'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$24#1#7???????'$39##1!$2-98,8#8!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2-1>0#8,$2-1:0#20'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40,$2:#8#38)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1,11;!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,5#42:18#44000#;>8;0#63=<4#63=<4!#!!,5#42:18#44000#;>8;0#63=<4#63=<4#5=#63=<4,20##429<0+$2-130$3$4$10<$10=$10>&6&5#&9$25#2#1+$2#48$2:#40$111$112$113$114$115$116+$2#48#1+$2-78+$2-78$25#1$18$19&9$25#2+$2#28$117$118$119$11:,,5=!$2#28,1&8&9$2;#?=&9$25#2!$2#38,8$24'$39#1#1!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8$39!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42580!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2-90,8$2:'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$24#1#7???????'$39##1!$2-98,8#8!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#40,8#!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2-1>0#8,$2-1:0#20'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40,$2:#8#38)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1,11;!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PCase ce2 (0) (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 409028 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 409028 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_19bd26.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_19bd26.IT BndT_Ns_000.SegItab_Ns_19bd26.IT_sound BF NX0 BR XSTEP F0 PSS plan 277500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twD2b.

Module LibSegNs_twD2c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_a8b108.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_a8b108.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-130$3$4$<=$<>$<?$3=+$2#48$=2$=3$=4$=5$=6$=7$=8$=9+$2#48#1+$2-78+$2-78$25#1$18$19$3;+$2#28$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",42'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$24#1#7???????'$39##1'$37##??'&9$37#1#1#1!$2#28,1&8&9$2;#?=&9$25#2!$2#38,8$24!$2#30,8#1!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2-98,8#8!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#40,8#!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2-1>0#;0"%pstring).
Definition ss0 : sym_state := SS 272832 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#42:18#5=#42:18,20#$28$2$3$4$<=$<>$<?$8$9#$=3$=4$=5$=6$=7$=8$=9$12$13$14$15$16$17$18$19$1:$1;$>4$>5$>6$>7,,42'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$24#1#7???????'$39##1'$37##??'&9$37#1#1#1!$2#28,1&8&9$2;#?=&9$25#2!$2#38,8$24!$2#30,8#1!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2-98,8#8!$2-:0,8#1!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#40,8#!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2-1>0#;0,?;!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 272920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_a8b108.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 272832 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_a8b108.IT BndT_Ns_001.SegItab_Ns_a8b108.IT_sound BF NX0 BR XSTEP F0 PSS plan 272832 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twD2c.

Module LibSegNs_twDa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2362cb.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2362cb.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#2!$2#58,8#8!$2#60,8$29'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40!$29#,8$24!$29#8,8$26,$29#10#30!$2-88,1$32'$32##??!$2-:8,1$33'$33##??!$2-<8,1$34'$34##??!$2->8,1$35'$35##??'$26#1#40000000"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#;>8;0#5=#;>8;0,20##43;?<+$2-170$3$4$5$6$7+$2#48+$2-:8#40#+$2-<8#1#1$?$10$11#2#1+$2-78+$2-78$25#1$18$19$1:+$2#28$1<$1=$1>$1?,,40!$2-90,8#!$2-98,8#8!$2-:0,8#2!$2-:8,1&8&9$25#2&9+@#2&6$33#1#1#?=!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8@#4&6$32#2!$2-138,8#424=8!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-88,1@#4&6$32#2!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#90,$2-130#88,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#2!$2#58,8#8!$2#60,8$29'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$32##??'$33##??!$2-<8,1$34'$34##??!$2->8,1$35'$35##??'$26#1#40000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 780464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2362cb.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2362cb.IT BndT_Ns_000.SegItab_Ns_2362cb.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twDa.

End BndP_Ns_080.
