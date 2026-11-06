(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Ns_114.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_114 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdB3ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCd3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdCf3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdDd3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE03ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdE13ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114>LibSegNs_vdE1w3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdJf3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWd3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114=LibSegNs_vdWf3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114<LibSegNs_vdZ3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114?LibSegNs_vd_gtA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtA23ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_114@LibSegNs_vd_gtE13ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNs_vdB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263260].
Definition STOPS1 : list Z := [263260] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$9$:$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 263256 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4045<#4045<#5=#4045<,20#$1+$2-30$3$4$5$6$7$:$9$29$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263260 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263256 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263256 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdB.

Module LibSegNs_vdCd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263308].
Definition STOPS1 : list Z := [263308] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$9$29#$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 263268 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4048<#4048<#5=#4048<,20#$1+$2-30$3$4$5$6$7$:+$:#8$29#$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263308 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263268 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263268 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdCd.

Module LibSegNs_vdCf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$9$29#1$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 263268 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-42), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-42), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##4047<+$2-30$3$4$5$6$7$:+$:#8$29+$2-2:$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;!$2-2:,1#<:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263268 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263268 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdCf.

Module LibSegNs_vdDd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$29$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$24#7???7?800000#7?????????=0&$24#8"%pstring).
Definition ss0 : sym_state := SS 263312 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-41), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-41), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##404:0+$2-30$3$4$5$6$7$:$24$29+$2-29$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$2-29,1#<;'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$24#7???7?800000#7?????????=0&$24#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263312 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263312 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdDd.

Module LibSegNs_vdE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263380].
Definition STOPS1 : list Z := [263380] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$26'$26##800000000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 263340 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#404=4#404=4#5=#404=4,20#$2<+$2-30$3$4$5$6$7$2=$2>#1$26$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$26'$26##800000000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263380 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263340 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263340 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdE0.

Module LibSegNs_vdE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263380].
Definition STOPS1 : list Z := [263380] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38!$27-8,8$2:'$2:#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 263340 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 39), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 39), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#404=4#404=4#5=#404=4,20#$2<+$2-30$3$4$5$6$7$2=$2>#1+$2:#1$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$27-8,8+$2:#1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38'$2:#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263380 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263340 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263340 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdE1.

Module LibSegNs_vdE1w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263380].
Definition STOPS1 : list Z := [263380] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38!$27-8,8^#?#???????????????!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 263340 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 39), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 39), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#404=4#404=4#5=#404=4,20#$2<+$2-30$3$4$5$6$7$2=$2>#1#$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$27-8,8#'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263380 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263340 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263340 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdE1w.

Module LibSegNs_vdJf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263340].
Definition STOPS1 : list Z := [263340] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48)].
Definition ss0 : sym_state := SS 263304 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#404:<#404:<#5=#404:<,20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#7?????????<0&$2#10($2-30#30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263340 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263304 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263304 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdJf.

Module LibSegNs_vdWd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [270880].
Definition STOPS1 : list Z := [270880] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483072 140737488355280;
   KAlign (EVar 36) 8].
Definition ss0 : sym_state := SS 263332 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42220#42220#5=#42220,20##404:<+$2-30$3$4$5$6$7$:$24$24$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$24#7???7?800000#7?????????=0&$24#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 270880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263332 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263332 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdWd.

Module LibSegNs_vdWf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [270744].
Definition STOPS1 : list Z := [270744] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483072 140737488355280;
   KAlign (EVar 36) 8].
Definition ss0 : sym_state := SS 263296 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42198#42198#5=#42198,20##40488+$2-30$3$4$5$6$7$:$24$24$38$39$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$24#7???7?800000#7?????????=0&$24#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 270744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263296 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263296 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdWf.

Module LibSegNs_vdZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263392].
Definition STOPS1 : list Z := [263392] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48)].
Definition ss0 : sym_state := SS 263388 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#404>0#404>0#5=#404>0,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#7?????????<0&$2#10($2-30#30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263392 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdZ.

Module LibSegNs_vd_gtA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255792].
Definition STOPS1 : list Z := [255792] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 50; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483200 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-144)) (ELit 144);
   KRange (EVar 50) 0 255].
Definition ss0 : sym_state := SS 255776 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 144)].
Definition F0L : list SR.region := [((EVar 2), (-144), 144)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>730#3>730#5=#3>730,20#$1+$2-90$3$4$5$6$7$8$9$32$22$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-90#90'$32##??,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255792 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255776 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255776 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtA.

Module LibSegNs_vd_gtA2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255800].
Definition STOPS1 : list Z := [255800] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$8$9$:$22$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483200 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-144)) (ELit 144)].
Definition ss0 : sym_state := SS 255796 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>738#3>738#5=#3>738,20#$1+$2-90$3$4$5$6$7$22$9$:$22$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800080#800000000000&$2#10($2-90#90,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255800 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255796 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255796 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtA2.

Module LibSegNs_vd_gtE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255952].
Definition STOPS1 : list Z := [255952] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$3<$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255984 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>7=0#3>7=0#5=#3>7=0,20#$23+$2-90$3$4$5$6$7$24$25$3<$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255984 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255984 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtE1.

End BndP_Ns_114.
Module BndP_Ns_115.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_115 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE22BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE25XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtE23ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtF3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtL3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtM3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115?LibSegNs_vd_gtP3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ13ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ23ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ33ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115@LibSegNs_vd_gtZ43ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_115<LibSegNs_vkR3ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNs_vd_gtE2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255952].
Definition STOPS1 : list Z := [255952] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255936 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>7=0#3>7=0#5=#3>7=0,20#$23+$2-90$3$4$5$6$7$24$25#1$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255936 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255936 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtE2.

Module LibSegNs_vd_gtF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255988].
Definition STOPS1 : list Z := [255988] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$32$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255968 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>7?4#3>7?4#5=#3>7?4,20##3>7?0+$2-90$3$4$5$6$7$22$32$32$22#$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255988 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255968 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtF.

Module LibSegNs_vd_gtL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255912].
Definition STOPS1 : list Z := [255912] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25!$2-24,4$37'$37#1#15"%pstring).
Definition ss0 : sym_state := SS 255908 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>7:8#3>7:8#5=#3>7:8,20#$1+$2-90$3$4$5$6$7$22$9$:$37$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25!$2-24,4$37'$37#1#15,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255912 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255908 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255908 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtL.

Module LibSegNs_vd_gtM.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255896 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3>7:4+$2-90$3$4$5$6$7$22$9$21#2=$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255896 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255896 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtM.

Module LibSegNs_vd_gtP.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [253132].
Definition STOPS1 : list Z := [253132] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$37$38$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255916 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3=<<<#3=<<<#5=#3=<<<,20##3>7<0+$2-90$3$4$5$6$7$22$9+$2-8<$37$38^#?#??????????????<#11$22$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 253132 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255916 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255916 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtP.

Module LibSegNs_vd_gtZ1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255812 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3>750+$2-90$3$4$5$6$7$22$9$21#30$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255812 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtZ1.

Module LibSegNs_vd_gtZ2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255824 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3>75<+$2-90$3$4$5$6$7$22$9$21#2>$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255824 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255824 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtZ2.

Module LibSegNs_vd_gtZ3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255836 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3>768+$2-90$3$4$5$6$7$22$9$21#30$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255836 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtZ3.

Module LibSegNs_vd_gtZ4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(255776, 53%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [255952].
Definition STOPS1 : list Z := [255952] ++ ENDS.
Definition NX0 : nat := 160.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 255848 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>7=0#3>7=0#5=#3>7=0,20#$23+$2-90$3$4$5$6$7$24$25#1$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800080#800000000000&$2#10($2-90#90'$22#7???7?800000#7??????????8)$2-90#90$22##8!$22#,8$21!$2-8,8$23!$2-10,8$24!$2-18,8$25,:0!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 255952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 255848 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 255848 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vd_gtZ4.

Module LibSegNs_vkA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(264208, 10%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [264408].
Definition STOPS1 : list Z := [264408] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483088 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16)].
Definition ss0 : sym_state := SS 264208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#408=8#408=8#5=#408=8,20##40828+$2-10$3$4$5$6$7$8$9$:$;#$<$=$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4!$2-8,8$1'$2#7???7?800010#800000000000&$2#10($2-10#10,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264408 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 264208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vkA.

Module LibSegNs_vkR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(264208, 10%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [264244].
Definition STOPS1 : list Z := [264244] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4$5$6$7$8$9$37$38$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483088 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KWord (SA (EVar 2) (-8)) 8 (EVar 44)].
Definition ss0 : sym_state := SS 264232 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40834#40834#5=#40834,20#$2<$2$3$4$5$6$7$8$9#1$38$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800010#800000000000&$2#10($2-10#10!$2-8,8$2<,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264244 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264232 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 264232 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vkR.

End BndP_Ns_115.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001.
Module BndP_Ns_050.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_050 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_7534fd2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boA3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050?LibSegNs_mp_boF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050@LibSegNs_mp_boG03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs102BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs102BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs105XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs104planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050BLibSegNs_mp_boGs103kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_050ALibSegNs_mp_boGs83kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_mp_boA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [289496].
Definition STOPS1 : list Z := [289496] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 12; EVar 38; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$24#<,4$21'$21##3??!$24#140,4#400($24#<#4"%pstring).
Definition ss0 : sym_state := SS 287860 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 36), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 36), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46:=8#46:=8#5=#46:=8,20##464<8+$2-70$3$4$5$6$7$24$26$24$<$26+$21#1$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$24#<,4+$21#1!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18'$21##3??!$24#140,4#400($24#<#4,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289496 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287860 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287860 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boA.

Module LibSegNs_mp_boE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [268884].
Definition STOPS1 : list Z := [268884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 12; EVar 38; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$24#<,4#400!$24#140,4#400($24#<#4"%pstring).
Definition ss0 : sym_state := SS 287860 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 36), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 36), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:54#41:54#5=#41:54,20##46630+$2-70$3$4$5$6$7$24$26$26#8$<#401$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#<,4#401!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$24#140,4#400($24#<#4,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287860 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287860 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boE.

Module LibSegNs_mp_boF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [288200].
Definition STOPS1 : list Z := [288200] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8$35!$24#188,8+$35$33'$33#18#10000'$35#1000#7??????00000&$35#8($35##18)$2-80#80$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 53), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 53), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#465<8#465<8#5=#465<8,20#$1+$2-70$3$4$5$6$7$24$26#3+$35$33$<$=$>$?$10$11$25$30$14+$35#18$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$35#10,8#!$35#8,8$30!$35#,4#3'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8$35!$24#188,8+$35$33'$33#18#10000'$35#1000#7??????00000&$35#8($35##18)$2-80#80$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$24#8,1#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288200 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boF.

Module LibSegNs_mp_boG0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [288288].
Definition STOPS1 : list Z := [288288] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#8,1#"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46620#46620#5=#46620,20#$28$2$3$4$5$6$7$29$2:$30#$<$=$>$?$10$11$2;$2<$2=$2>$2?$17$18$19$1:$1;$1<$1=$1>$1?,,1;'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#8,1#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288288 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boG0.

Module LibSegNs_mp_boGs0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#18!$24#188,8+$22#18'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#2$26#30#40#1#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#18+$22#18$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#18!$24#188,8+$22#18'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs0.

Module LibSegNs_mp_boGs1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#30!$24#188,8+$22#30'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#4$26#60#80#2#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#30+$22#30$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#30!$24#188,8+$22#30'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs1.

Module LibSegNs_mp_boGs10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#6000!$24#188,8+$22#6000'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#800$26#<000#10000#400#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#6000+$22#6000$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#6000!$24#188,8+$22#6000'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs10.

Module LibSegNs_mp_boGs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#60!$24#188,8+$22#60'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#8$26#<0#100#4#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#60+$22#60$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#60!$24#188,8+$22#60'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs2.

Module LibSegNs_mp_boGs3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<0!$24#188,8+$22#<0'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#10$26#180#200#8#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#<0+$22#<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<0!$24#188,8+$22#<0'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs3.

Module LibSegNs_mp_boGs4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#180!$24#188,8+$22#180'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#20$26#300#400#10#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#180+$22#180$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#180!$24#188,8+$22#180'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs4.

Module LibSegNs_mp_boGs5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#300!$24#188,8+$22#300'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#40$26#600#800#20#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#300+$22#300$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#300!$24#188,8+$22#300'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs5.

Module LibSegNs_mp_boGs6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#600!$24#188,8+$22#600'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#80$26#<00#1000#40#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#600+$22#600$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#600!$24#188,8+$22#600'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs6.

Module LibSegNs_mp_boGs7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<00!$24#188,8+$22#<00'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#100$26#1800#2000#80#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#<00+$22#<00$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<00!$24#188,8+$22#<00'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs7.

Module LibSegNs_mp_boGs8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7534fd.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7534fd.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#1800!$24#188,8+$22#1800'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 287944 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 2), (-128), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 2), (-128), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#200$26#3000#4000#100#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#1800+$22#1800$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46558!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#1800!$24#188,8+$22#1800'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7534fd.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7534fd.IT BndT_Ns_001.SegItab_Ns_7534fd.IT_sound BF NX0 BR XSTEP F0 PSS plan 287944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_boGs8.

End BndP_Ns_050.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_001.
Module BndP_Ns_044.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_044 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_ddbfd22ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044<LibSegNs_btN3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044=LibSegNs_btV13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btV1w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW322BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW322BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW325XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW324planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_btW323kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_74cfe92ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAc3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044?LibSegNs_enEAp23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044@LibSegNs_enEAp2w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEAr3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bd67f12ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_044>LibSegNs_enEOc3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_btN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ddbfd2.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ddbfd2.IT.
Definition ENDS : list Z := [265656].
Definition STOPS1 : list Z := [265656] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$24$37$38$<$=$>$?$10$11$26$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KRange (EVar 36) 1 140737488355327;
   KRange (EVar 38) 2 536870911].
Definition ss0 : sym_state := SS 265676 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40=;8#40=;8#5=#40=;8,20#$1+$2-30$3$4$5$6$7$:+$24#1$37$38$<$=$>$?$10$11+$26-1$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800030#800000000000&$2#10'$24#1#7???????????'$26#2#1???????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 265656 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ddbfd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265676 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ddbfd2.IT BndT_Ns_002.SegItab_Ns_ddbfd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 265676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_btN.

Module LibSegNs_btV0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ddbfd2.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ddbfd2.IT.
Definition ENDS : list Z := [265740].
Definition STOPS1 : list Z := [265740] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$39$37$38$<$=$>$?$10$11$3:$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800030#800000000000&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$26'$26##800000000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 265688 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40>0<#40>0<#5=#40>0<,20#$2<$2$3$4$5$6$7$2=$2>#1$26$<$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?800030#800000000000&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$26'$26##800000000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 265740 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ddbfd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265688 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ddbfd2.IT BndT_Ns_002.SegItab_Ns_ddbfd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 265688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_btV0.

Module LibSegNs_btV1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ddbfd2.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ddbfd2.IT.
Definition ENDS : list Z := [265740].
Definition STOPS1 : list Z := [265740] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$39$37$38$<$=$>$?$10$11$3:$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800030#800000000000&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38!$27-8,8$2:'$2:#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 265688 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 39), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 39), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40>0<#40>0<#5=#40>0<,20#$2<$2$3$4$5$6$7$2=$2>#1+$2:#1$<$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$27-8,8+$2:#1'$2#7???7?800030#800000000000&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38'$2:#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 265740 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ddbfd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265688 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ddbfd2.IT BndT_Ns_002.SegItab_Ns_ddbfd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 265688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_btV1.

Module LibSegNs_btV1w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ddbfd2.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ddbfd2.IT.
Definition ENDS : list Z := [265740].
Definition STOPS1 : list Z := [265740] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$39$37$38$<$=$>$?$10$11$3:$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800030#800000000000&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38!$27-8,8^#?#???????????????!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 265688 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 39), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 39), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40>0<#40>0<#5=#40>0<,20#$2<$2$3$4$5$6$7$2=$2>#1#$<$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$27-8,8#'$2#7???7?800030#800000000000&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-30#30)$27-18#18$:##38!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 265740 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ddbfd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265688 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ddbfd2.IT BndT_Ns_002.SegItab_Ns_ddbfd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 265688 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_btV1w.

Module LibSegNs_btW16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ddbfd2.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ddbfd2.IT.
Definition ENDS : list Z := [269036].
Definition STOPS1 : list Z := [269036] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$;$37$38$<$=$>$?$10$11$22+$:#8$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KRange (EVar 34) 0 18446744073709551615].
Definition ss0 : sym_state := SS 265632 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:><#41:><#5=#41:><,20##40=:<+$2-30$3$4$5$6$7$:$;$22+$:#8$<$=$>$?$10$11$22+$:#8$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#800000000000&$2#10'$22#^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269036 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ddbfd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ddbfd2.IT BndT_Ns_002.SegItab_Ns_ddbfd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 265632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_btW16.

Module LibSegNs_btW32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ddbfd2.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ddbfd2.IT.
Definition ENDS : list Z := [269136].
Definition STOPS1 : list Z := [269136] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$;$37$38$<$=$>$?$10$11$22+$:#8$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KRange (EVar 34) 0 18446744073709551615].
Definition ss0 : sym_state := SS 265552 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41;50#41;50#5=#41;50,20##40=5<+$2-30$3$4$5$6$7$:$;%0$22#+$:#8$<$=$>$?$10$11$22+$:#8$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#800000000000&$2#10'$22#^#?#???????????????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269136 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ddbfd2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 265552 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ddbfd2.IT BndT_Ns_002.SegItab_Ns_ddbfd2.IT_sound BF NX0 BR XSTEP F0 PSS plan 265552 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_btW32.

Module LibSegNs_enEAa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_74cfe9.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_74cfe9.IT.
Definition ENDS : list Z := [261952].
Definition STOPS1 : list Z := [261952] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0!$:#30,4$24'$24#1#1000!$27-18,4$25'$25##????????!$27-10,8$2;'$2;#^#?#???????????????!$27-8,8$2:'$2:#^#?#???????????????)$27-18#18$2-30#30)$27-18#18$:##38"%pstring).
Definition ss0 : sym_state := SS 261900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3??40#3??40#5=#3??40,20#$1+$2-30$3$4$5$6$7$8$9$:$27$<$26$2;],,4$25$2:$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$:#30,4+$24-1!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0'$24#1#1000!$27-18,4$25'$25##????????!$27-10,8$2;'$2;#^#?#???????????????!$27-8,8$2:'$2:#^#?#???????????????)$27-18#18$2-30#30)$27-18#18$:##38,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 261952 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_74cfe9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 261900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_74cfe9.IT BndT_Ns_001.SegItab_Ns_74cfe9.IT_sound BF NX0 BR XSTEP F0 PSS plan 261900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEAa.

Module LibSegNs_enEAc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_74cfe9.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_74cfe9.IT.
Definition ENDS : list Z := [268884].
Definition STOPS1 : list Z := [268884] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KRange (EVar 11) 6 7;
   KRange (EVar 12) 140735332483072 140737488355328].
Definition ss0 : sym_state := SS 261980 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:54#41:54#5=#41:54,20##3??64+$2-30$3$4$5$6$7$8$9$<$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800030#7?????????<0&$2#10'$;#6#7'$<#7???7?800000#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 268884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_74cfe9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 261980 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_74cfe9.IT BndT_Ns_001.SegItab_Ns_74cfe9.IT_sound BF NX0 BR XSTEP F0 PSS plan 261980 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEAc.

Module LibSegNs_enEAp1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_74cfe9.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_74cfe9.IT.
Definition ENDS : list Z := [262008].
Definition STOPS1 : list Z := [262008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:+$26#18$<$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#7?????????>8&$26#8!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 262012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (32), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (32), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3??78#3??78#5=#3??78,20#$2<$2$3$4$5$6$7$2=$2>#1+$26#18$26$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$:#20,8$26'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#7?????????>8&$26#8!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 262008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_74cfe9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262012 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_74cfe9.IT BndT_Ns_001.SegItab_Ns_74cfe9.IT_sound BF NX0 BR XSTEP F0 PSS plan 262012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEAp1.

Module LibSegNs_enEAp2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_74cfe9.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_74cfe9.IT.
Definition ENDS : list Z := [262008].
Definition STOPS1 : list Z := [262008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$27$<$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38!$27-20,8$2?'$2?#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 262012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (32), ELit 8); ((EVar 39), (-32), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (32), 8); ((EVar 39), (-32), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3??78#3??78#5=#3??78,20#$2<$2$3$4$5$6$7$2=$2>#1$27+$27-18$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$27-20,8+$2?#1!$:#20,8+$27-18'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38'$2?#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 262008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_74cfe9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262012 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_74cfe9.IT BndT_Ns_001.SegItab_Ns_74cfe9.IT_sound BF NX0 BR XSTEP F0 PSS plan 262012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEAp2.

Module LibSegNs_enEAp2w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_74cfe9.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_74cfe9.IT.
Definition ENDS : list Z := [262008].
Definition STOPS1 : list Z := [262008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$27$<$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38!$27-20,8^#?#???????????????!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 262012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (32), ELit 8); ((EVar 39), (-32), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (32), 8); ((EVar 39), (-32), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3??78#3??78#5=#3??78,20#$2<$2$3$4$5$6$7$2=$2>#1$27+$27-18$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13!$27-20,8#!$:#20,8+$27-18'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 262008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_74cfe9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262012 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_74cfe9.IT BndT_Ns_001.SegItab_Ns_74cfe9.IT_sound BF NX0 BR XSTEP F0 PSS plan 262012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEAp2w.

Module LibSegNs_enEAr.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_74cfe9.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_74cfe9.IT.
Definition ENDS : list Z := [262008].
Definition STOPS1 : list Z := [262008] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KWord (SA (EVar 2) (-8)) 8 (EVar 44);
   KWord (SA (EVar 2) (-16)) 8 (EVar 45);
   KWord (SA (EVar 2) (-24)) 8 (EVar 46)].
Definition ss0 : sym_state := SS 261988 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3??78#3??78#5=#3??78,20#$2<$2$3$4$5$6$7$2=$2>#1$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'$2#7???7?800030#7?????????<0&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 262008 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_74cfe9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 261988 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_74cfe9.IT BndT_Ns_001.SegItab_Ns_74cfe9.IT_sound BF NX0 BR XSTEP F0 PSS plan 261988 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEAr.

Module LibSegNs_enEOa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bd67f1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bd67f1.IT.
Definition ENDS : list Z := [263964].
Definition STOPS1 : list Z := [263964] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0!$:#30,4$24'$24#1#1000!$27-18,4$25'$25##????????!$27-10,8$2;'$2;#^#?#???????????????!$27-8,8$2:'$2:#^#?#???????????????)$27-18#18$2-30#30)$27-18#18$:##38"%pstring).
Definition ss0 : sym_state := SS 263912 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 10), (48), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 10), (48), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4071<#4071<#5=#4071<,20#$1+$2-30$3$4$5$6$7$8$9$:$27$<$26$2;],,4$25$2:$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$:#30,4+$24-1!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0'$24#1#1000!$27-18,4$25'$25##????????!$27-10,8$2;'$2;#^#?#???????????????!$27-8,8$2:'$2:#^#?#???????????????)$27-18#18$2-30#30)$27-18#18$:##38,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263964 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bd67f1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263912 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bd67f1.IT BndT_Ns_002.SegItab_Ns_bd67f1.IT_sound BF NX0 BR XSTEP F0 PSS plan 263912 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEOa.

Module LibSegNs_enEOc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bd67f1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bd67f1.IT.
Definition ENDS : list Z := [268884].
Definition STOPS1 : list Z := [268884] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KRange (EVar 11) 6 7;
   KRange (EVar 12) 140735332483072 140737488355328].
Definition ss0 : sym_state := SS 263992 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:54#41:54#5=#41:54,20##40740+$2-30$3$4$5$6$7$8$9$<$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800030#7?????????<0&$2#10'$;#6#7'$<#7???7?800000#800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 268884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bd67f1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263992 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bd67f1.IT BndT_Ns_002.SegItab_Ns_bd67f1.IT_sound BF NX0 BR XSTEP F0 PSS plan 263992 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEOc.

End BndP_Ns_044.
Module BndP_Ns_113.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_113 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spA3ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spB3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spE3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spF3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spG3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_spR03ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_spS3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_syB3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq03ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq13ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_twq23ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113<LibSegNs_vdA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_113=LibSegNs_vdA33ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNs_spA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [288956; 288820; 288896; 288856].
Definition STOPS1 : list Z := [288956; 288820; 288896; 288856] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 35); (EVar 34); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 288772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5;#46818,20#$1+$2-20$3$4$5$6$7$8$9$21$23$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5=#468;<,20#$1$2$3$4$5$6$7$8$9##$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'&4&1$23##1#1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5;#4682<,20#$1+$2-20$3$4$5$6$7$23$21$21$24$22$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'&4&1$23##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5:#46858,20#$1+$2-20$3$4$5$6$7$23$21$21$24$22$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'&4&1$24##1#1#1'&4&1$23##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5;#46830,20#$1+$2-20$3$4$5$6$7$23$21$21$24$22$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'&4&1$24##1##'&4&1$23##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5:#46880,20#$1+$2-20$3$4$5$6$7$23$21$21$24$22$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'&4$24$23#1#1'&4&1$24##1##'&4&1$23##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,8#468;<#46834#46880#46858#468;<#46834#46880#46858#5:#46834,20#$1+$2-20$3$4$5$6$7$23$21$21$24$22$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'&4$24$23##'&4&1$24##1##'&4&1$23##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#120,8$24'$24##4000'$23#^#?#???????????????,38!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 3)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PEnd 1))))))).
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
Definition ps0 : SR.post_spec := SR.PS 288956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s10).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s10).
Definition ps1 : SR.post_spec := SR.PS 288820 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SR.PS 288896 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s6).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s6).
Definition ps3 : SR.post_spec := SR.PS 288856 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spA.

Module LibSegNs_spB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [288896; 288820].
Definition STOPS1 : list Z := [288896; 288820] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$23$21$2;$;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2:#1000#800000000000'$2;##4000'$23#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 288876 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (280), ELit 16)].
Definition F0L : list SR.region := [((EVar 33), (280), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46880#46834#46880#46834#5;#4687<,20#$1+$2-20$3$4$5$6$7$23$21$2:$2;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$21#120,8$2;!$21#118,8$2:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2:#1000#800000000000'$2;##4000'$23#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46880#46834#46880#46834#5:#46880,20#$1+$2-20$3$4$5$6$7$23$21$2:$2;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'&4$2;$23#1#1!$21#120,8$2;!$21#118,8$2:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2:#1000#800000000000'$2;##4000'$23#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46880#46834#46880#46834#5:#46834,20#$1+$2-20$3$4$5$6$7$23$21$2:$2;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'&4$2;$23##!$21#120,8$2;!$21#118,8$2:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#108,8$2:($21#118#10'$2:#1000#800000000000'$2;##4000'$23#1^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288896 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 288820 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288876 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spB.

Module LibSegNs_spE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [288956].
Definition STOPS1 : list Z := [288956] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$23$21$:$;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800020#800000000000&$2#10($2-20#20!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$22#7???7?800020#7?????????>8&$22#8)$2-20#20$22##18!$22#,8$29!$22#8,8+$29$28'$29##800000000000'$28##800000000000"%pstring).
Definition ss0 : sym_state := SS 288920 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#468;<#468;<#5=#468;<,20#$2<$2$3$4$5$6$7$2=$2>$29$28$<$=$>$?$10$11$2?$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'$2#7???7?800020#800000000000&$2#10($2-20#20!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$22#7???7?800020#7?????????>8&$22#8)$2-20#20$22##18!$22#,8$29!$22#8,8+$29$28'$29##800000000000'$28##800000000000,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spE.

Module LibSegNs_spF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [288840].
Definition STOPS1 : list Z := [288840] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$23$21$:$24$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#118,8$25,$21#100#8'$25#1000#800000000000'$23#1#4000'$24#1#4000"%pstring).
Definition ss0 : sym_state := SS 288820 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46848#46848#5=#46848,20#$1+$2-20$3$4$5$6$7$23$21$25+@-1$23$24+$23$38+$23$25$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#118,8$25,$21#100#8'$25#1000#800000000000'$23#1#4000'$24#1#4000,39!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288840 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288820 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288820 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spF.

Module LibSegNs_spG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [288956].
Definition STOPS1 : list Z := [288956] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$23$21$25$30$31$32$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?800020#800000000000&$2#10($2-20#20!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128($21#100#8($21#118#10'$30#^#?#???????????????'$31#^#?#???????????????'$32#^#?#???????????????'$25#^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 288840 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (256), ELit 8); ((EVar 33), (280), ELit 16)].
Definition F0L : list SR.region := [((EVar 33), (256), 8); ((EVar 33), (280), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#468;<#468;<#5=#468;<,20#$2<$2$3$4$5$6$7$2=$2>$25$23$31$32$>$?$10$11$2?$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13!$21#120,8$30!$21#118,8$32!$21#100,8$31'$2#7???7?800020#800000000000&$2#10($2-20#20!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128($21#100#8($21#118#10'$30#^#?#???????????????'$31#^#?#???????????????'$32#^#?#???????????????'$25#^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288840 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288840 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spG.

Module LibSegNs_spR0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [288896; 291092].
Definition STOPS1 : list Z := [288896; 291092] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$23$21$:$;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#110,8#4000!$21#108,8$2:'$2:#1000#800000000000'$23#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 288856 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46880#47114#46880#47114#5;#4685<,20#$1+$2-20$3$4$5$6$7$23$21$:$;#4000$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#110,8#4000!$21#108,8$2:'$2:#1000#800000000000'$23#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46880#47114#46880#47114#5:#46880,20#$1+$2-20$3$4$5$6$7$23$21$:$;#4000$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'&4#4000$23#1#1'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#110,8#4000!$21#108,8$2:'$2:#1000#800000000000'$23#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46880#47114#46880#47114#5=#47114,20##4686<+$2-20$3$4$5$6$7$23$21$21$2:#4000$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'&4#4000$23##'$2#7???7?800020#800000000000&$2#10($2-20#20'$21#7???7?800020#7????????>=8&$21#8)$2-20#20$21##128!$21#110,8#4000!$21#108,8$2:'$2:#1000#800000000000'$23#1^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288896 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 291092 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spR0.

Module LibSegNs_spS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(288772, 50%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [291320].
Definition STOPS1 : list Z := [291320] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$23$21$:$;$<$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800020#800000000000&$2#10($2-20#20'$22#7???7?800020#7?????????>8&$22#8)$2-20#20$22##18!$22#,8$27'$27##800000000000($22#8#8"%pstring).
Definition ss0 : sym_state := SS 288896 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 34), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 34), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#471?8#471?8#5=#471?8,20##46898+$2-20$3$4$5$6$7$23$21$21$22$23$=$>$?$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:!$22#8,8$27'$2#7???7?800020#800000000000&$2#10($2-20#20'$22#7???7?800020#7?????????>8&$22#8)$2-20#20$22##18!$22#,8$27'$27##800000000000($22#8#8,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291320 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288896 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 288896 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_spS.

Module LibSegNs_syA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(436020, 20%nat) ; (292004, 20%nat) ; (292084, 5%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [436044].
Definition STOPS1 : list Z := [436044] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KWord (SA (ELit 0) 880768) 1 (ELit 1)].
Definition ss0 : sym_state := SS 436020 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6:74<#6:74<#5=#6:74<,20#$1$2$3$4$5$6$7$8$9#<6;48$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1!##=7080,1#1,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 436044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 436020 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 436020 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_syA.

Module LibSegNs_syB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(436020, 20%nat) ; (292004, 20%nat) ; (292084, 5%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [436044].
Definition STOPS1 : list Z := [436044] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483088 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KImg 880768 880770;
   KWr (SA (ELit 0) 880768) (ELit 2)].
Definition ss0 : sym_state := SS 436020 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16); ((ELit 0), (880768), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16); ((ELit 0), (880768), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6:74<#6:74<#5=#6:74<,20#$1$2$3$4$5$6$7$8$9#<6;48#1#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7!##=7081,1#1!##=7080,1#1!$2-8,8$1'$2#7???7?800010#800000000000&$2#10($2-10#10(##=7080#2,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 436044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 436020 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 436020 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_syB.

Module LibSegNs_twq0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(278528, 63%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [278640].
Definition STOPS1 : list Z := [278776] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 33; EVar 34; ELit 10000000000000000000; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 814272;
   KRange (EVar 33) 1 1073741824].
Definition ss0 : sym_state := SS 278528 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#440?8#44070#5=#44070,20#$1$2$3$4^#8#9>8000000000000#????????+$21@-8:<72304/5$21#8:<72305$8$9#$22&4$22#^#8#:<7230489>80000#8:<72304#89>80000#8:<72305+$21+@-1&4$22#@-8:<72304/5$21#8:<72305$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,2%#10000#<6<<0'$21#1#40000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 278640 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278528 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 278528 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twq0.

Module LibSegNs_twq1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(278528, 63%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [278740; 278772].
Definition STOPS1 : list Z := [278776] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9#$22$<^#8#:<7230489>80000#8:<72304#89>80000#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 814272;
   KRange (EVar 33) 0 1073741824].
Definition ss0 : sym_state := SS 278640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5;#440;<,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#$22/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2%#10000#<6<<0'$21##40000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5;#440<0,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#$22/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1#1#1%#10000#<6<<0'$21##40000000,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5=#440?4,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#$22/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'&4+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000#1#1'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1#1#1%#10000#<6<<0'$21##40000000,50!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5=#440=4,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#++$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'&4+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000##'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1#1#1%#10000#<6<<0'$21##40000000,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5=#440=4,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#++$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1##%#10000#<6<<0'$21##40000000,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s5).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s5).
Definition ps0 : SR.post_spec := SR.PS 278772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 278740 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 278740 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 278640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twq1.

Module LibSegNs_twq2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(278528, 63%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [278740; 278772].
Definition STOPS1 : list Z := [278776] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; ELit 0; EVar 35; EVar 36; ELit 10000000000000000000; EVar 33; EVar 34; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 814272].
Definition ss0 : sym_state := SS 278740 regs0 [] kn0 NX0.
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

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#440><,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1&4$22^#8#:<7230489>80000+$22^#7#538=<?;76180000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1%#10000#<6<<0,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5;#440?0,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1&4$22^#8#:<7230489>80000+$22^#7#538=<?;76180000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'&4&1+$21@-1&4$22^#8#:<7230489>80000##1#1#1%#10000#<6<<0,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5=#440?4,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1&4$22^#8#:<7230489>80000+$22^#7#538=<?;76180000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4$23^#8#:<7230489>80000#1#1'&4&1+$21@-1&4$22^#8#:<7230489>80000##1#1#1%#10000#<6<<0,50!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5=#440=4,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1&4$22^#8#:<7230489>80000+$22^#7#538=<?;76180000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4$23^#8#:<7230489>80000##'&4&1+$21@-1&4$22^#8#:<7230489>80000##1#1#1%#10000#<6<<0,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#440?8#440=4#440?4#5=#440=4,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1&4$22^#8#:<7230489>80000+$22^#7#538=<?;76180000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'&4&1+$21@-1&4$22^#8#:<7230489>80000##1##%#10000#<6<<0,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s5).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s5).
Definition ps0 : SR.post_spec := SR.PS 278772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 278740 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 278740 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278740 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 278740 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twq2.

Module LibSegNs_vdA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263240].
Definition STOPS1 : list Z := [263240] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 263224 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40448#40448#5=#40448,20#$1+$2-30$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263240 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263224 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263224 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdA.

Module LibSegNs_vdA3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(263224, 43%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [263252].
Definition STOPS1 : list Z := [263252] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 263248 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40454#40454#5=#40454,20#$1+$2-30$3$4$5$6$7$:$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263248 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 263248 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vdA3.

End BndP_Ns_113.
Module BndP_Ns_097.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_097 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_dbc5142ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn642BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn642BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn645XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn644planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJn643kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp322BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp322BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp325XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp324planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp642BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp642BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp645XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp644planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097?LibSegNs_viJp643kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_7efbb42ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsA03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vsE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vsE1w3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_ecf95b2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA322BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA322BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA325XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA324planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA642BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA642BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA645XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA644planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097>LibSegNs_vuA643kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_097=LibSegNs_vuA83kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_viJn64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_dbc514.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_dbc514.IT.
Definition ENDS : list Z := [263020].
Definition STOPS1 : list Z := [263020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48)].
Definition ss0 : sym_state := SS 262944 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4036<#4036<#5=#4036<,20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#7?????????<0&$2#10($2-30#30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_dbc514.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262944 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_dbc514.IT BndT_Ns_002.SegItab_Ns_dbc514.IT_sound BF NX0 BR XSTEP F0 PSS plan 262944 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_viJn64.

Module LibSegNs_viJp16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_dbc514.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_dbc514.IT.
Definition ENDS : list Z := [263020].
Definition STOPS1 : list Z := [263020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48)].
Definition ss0 : sym_state := SS 263108 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4036<#4036<#5=#4036<,20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#7?????????<0&$2#10($2-30#30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_dbc514.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263108 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_dbc514.IT BndT_Ns_002.SegItab_Ns_dbc514.IT_sound BF NX0 BR XSTEP F0 PSS plan 263108 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_viJp16.

Module LibSegNs_viJp32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_dbc514.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_dbc514.IT.
Definition ENDS : list Z := [263020].
Definition STOPS1 : list Z := [263020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48)].
Definition ss0 : sym_state := SS 263180 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4036<#4036<#5=#4036<,20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#7?????????<0&$2#10($2-30#30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_dbc514.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 263180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_dbc514.IT BndT_Ns_002.SegItab_Ns_dbc514.IT_sound BF NX0 BR XSTEP F0 PSS plan 263180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_viJp32.

Module LibSegNs_viJp64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_dbc514.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_dbc514.IT.
Definition ENDS : list Z := [263020].
Definition STOPS1 : list Z := [263020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355264;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48)].
Definition ss0 : sym_state := SS 262880 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4036<#4036<#5=#4036<,20#$1+$2-30$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800030#7?????????<0&$2#10($2-30#30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 263020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_dbc514.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262880 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_dbc514.IT BndT_Ns_002.SegItab_Ns_dbc514.IT_sound BF NX0 BR XSTEP F0 PSS plan 262880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_viJp64.

Module LibSegNs_vsA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [273212].
Definition STOPS1 : list Z := [273212] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (ELit 0); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-160)) (ELit 160);
   KRange (EVar 10) 140735332483072 140737488355272;
   KAlign (EVar 10) 8;
   KWr (SA (EVar 10) 0) (ELit 56);
   KDisj (SA (EVar 2) (-160)) (ELit 160) (SA (EVar 10) 0) (ELit 56)].
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42;3<#42;3<#5=#42;3<,20##40:50+$2-:0$3$4$5$6$7$:$>$:$;##7$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 273212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264408 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264408 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vsA0.

Module LibSegNs_vsE0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [264848].
Definition STOPS1 : list Z := [264848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$39$37$38$3:$3;$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38!$:#18,8$26!$:#20,8$26'$26##800000000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264784 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40:90#40:90#5=#40:90,20#$2<$2$3$4$5$6$7$2=$2>#1$26$3:$3;$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38!$:#18,8$26!$:#20,8$26'$26##800000000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264784 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vsE0.

Module LibSegNs_vsE1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [264848].
Definition STOPS1 : list Z := [264848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$39$37$38$3:$3;$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-:0#:0)$27-18#18$:##38!$27-8,8$2:'$2:#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 39), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 39), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40:90#40:90#5=#40:90,20#$2<$2$3$4$5$6$7$2=$2>#1+$2:#1$3:$3;$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$27-8,8+$2:#1'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-:0#:0)$27-18#18$:##38'$2:#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264784 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vsE1.

Module LibSegNs_vsE1w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [264848].
Definition STOPS1 : list Z := [264848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$39$37$38$3:$3;$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-:0#:0)$27-18#18$:##38!$27-8,8^#?#???????????????!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264784 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 39), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 39), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40:90#40:90#5=#40:90,20#$2<$2$3$4$5$6$7$2=$2>#1#$3:$3;$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$27-8,8#'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-:0#:0$:##38!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)$27-18#18$2-:0#:0)$27-18#18$:##38!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264784 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264784 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vsE1w.

Module LibSegNs_vuA16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ecf95b.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ecf95b.IT.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#100#????'$<##"%pstring).
Definition ss0 : sym_state := SS 262160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##40188+$2-30$3$4$5$6$7$:$;$29+$2-23$<$=$>$?$10$11+$:#8$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-23,1#<=!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#100#????'$<##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ecf95b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ecf95b.IT BndT_Ns_002.SegItab_Ns_ecf95b.IT_sound BF NX0 BR XSTEP F0 PSS plan 262160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vuA16.

Module LibSegNs_vuA32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ecf95b.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ecf95b.IT.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#10000#????????'$<##"%pstring).
Definition ss0 : sym_state := SS 262160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##401:8+$2-30$3$4$5$6$7$:$;$29+$2-22$<$=$>$?$10$11+$:#8$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-22,1#<>!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#10000#????????'$<##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ecf95b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ecf95b.IT BndT_Ns_002.SegItab_Ns_ecf95b.IT_sound BF NX0 BR XSTEP F0 PSS plan 262160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vuA32.

Module LibSegNs_vuA5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ecf95b.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ecf95b.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$<#5#5"%pstring).
Definition ss0 : sym_state := SS 262160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40104+$2-30$3$4$5$6$7$:$;$:$;#$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$<#5#5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ecf95b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ecf95b.IT BndT_Ns_002.SegItab_Ns_ecf95b.IT_sound BF NX0 BR XSTEP F0 PSS plan 262160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vuA5.

Module LibSegNs_vuA64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ecf95b.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ecf95b.IT.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#100000000^#?#???????????????'$<##"%pstring).
Definition ss0 : sym_state := SS 262160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##400>4+$2-30$3$4$5$6$7$:$;$29+$2-21$<$=$>$?$10$11+$:#8$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-21,1#<?!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#100000000^#?#???????????????'$<##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ecf95b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ecf95b.IT BndT_Ns_002.SegItab_Ns_ecf95b.IT_sound BF NX0 BR XSTEP F0 PSS plan 262160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vuA64.

Module LibSegNs_vuA7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ecf95b.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ecf95b.IT.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;##7?'$<##"%pstring).
Definition ss0 : sym_state := SS 262160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##4013<+$2-30$3$4$5$6$7$:$;$29+$2-26$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-26,1$;!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;##7?'$<##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ecf95b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ecf95b.IT BndT_Ns_002.SegItab_Ns_ecf95b.IT_sound BF NX0 BR XSTEP F0 PSS plan 262160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vuA7.

Module LibSegNs_vuA8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ecf95b.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ecf95b.IT.
Definition ENDS : list Z := [269572].
Definition STOPS1 : list Z := [269572] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#80#??'$<##"%pstring).
Definition ss0 : sym_state := SS 262160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=04#41=04#5=#41=04,20##4012<+$2-30$3$4$5$6$7$:$;$29+$2-25$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-25,1#<<!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38!$:#8,8$29)$2-30#30$:##38'$29#7???7?800000#7?????????>8&$29#8'$;#80#??'$<##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269572 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ecf95b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 262160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ecf95b.IT BndT_Ns_002.SegItab_Ns_ecf95b.IT_sound BF NX0 BR XSTEP F0 PSS plan 262160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vuA8.

End BndP_Ns_097.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_002.
Module BndP_Ns_081.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_081 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_9298952ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDb3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_5c0ec12ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDc3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_6d2d032ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDd3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_7b5ef12ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDe3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_a8b1082ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twDg3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_88783e2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIa3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIb3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twIc3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_56547e2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081>LibSegNs_twhD03kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_57e41b2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1L3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_dff6272ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081?LibSegNs_twhD1S3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_ad16692ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0155;BndP_Ns_081=LibSegNs_twhL3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_twDb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_929895.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_929895.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-170$3$4$<=$<>$<?+$2#48+$2-:8$2:$=3$=4$=5$=6$=7$=8$=9#2#1+$2-78+$2-78$25#1$18$19$1:+$2#28$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",49'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000!$2-90,8#!$2-98,8#8!$2-:0,8#2!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8@#4&6$32#2!$2-138,8#424=8!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-88,1@#4&6$32#2!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-170#20,$2-130#88,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#2!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2-<8,1$34!$2->8,1$35!$2-:8,1$37,$2-1>0#70'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40,$2:##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1"%pstring).
Definition ss0 : sym_state := SS 277500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96); ((EVar 42), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96); ((EVar 42), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,5#42:18#44000#;>8;0#63=<4#;>8;0!#!!,5#42:18#44000#;>8;0#63=<4#;>8;0#5=#;>8;0,20##43;?<+$2-170$3$4$?<$?=$?>+$2-:8+$2-<8#40#+$2->8#1#2#1+$2-78@#4&6$32#2#2^#8#:<7230489>80000+$2-78+$2-78$2:$29+$2#58$19&9$25#2+$2#28$107$108$109$10:,,51!$2-;0,8#!$2-;8,8#8!$2-<0,8#2!$2-<8,1&9+@#2&6$34#1#1#?=!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#4277<!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-170#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#2!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2-1>0#70'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40,$2:#10#30)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1,10;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_929895.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_929895.IT BndT_Ns_001.SegItab_Ns_929895.IT_sound BF NX0 BR XSTEP F0 PSS plan 277500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twDb.

Module LibSegNs_twDc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_5c0ec1.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_5c0ec1.IT.
Definition ENDS : list Z := [278528].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-170$3$4$<=$<>$<?+$2-:8+$2-<8$23$=3$=4$=5$=6$=7$=8$=9#2^#8#:<7230489>80000+$2-78+$2-78$2:$29+$2#58$19$3;+$2#28$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5;'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1!$2-;0,8#!$2-;8,8#8!$2-<0,8#2!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#4277<!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-170#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#2!$2#58,8#8!$2#60,8$29!$29#,8$24!$29#8,8$26,$29#10#30!$2->8,1$35,$2:#10#30!$2-<8,1$38,$2-1>0#70'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40,$23##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2"%pstring).
Definition ss0 : sym_state := SS 277500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96); ((EVar 42), (0), ELit 64); ((EVar 35), (0), ELit 64); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96); ((EVar 42), (0), 64); ((EVar 35), (0), 64); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",7!!,5#42:18#44000#;>8;0#63=<4#44000!#!!,5#42:18#44000#;>8;0#63=<4#44000!$!!,5#42:18#44000#;>8;0#63=<4#44000!#!!,5#42:18#44000#;>8;0#63=<4#44000#5=#44000,20##428=<+$2-130$3$4$11<$11=$11>$29+$2#48+$2#48$26$24^#8#:<7230489>80000$123$124$125$126+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78$127$128$129$12:,,77!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#38,8$24!$2#40,8$26!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42808#$29##8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?8#<,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40,$23#10#30)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2,12;!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 278528 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_5c0ec1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_5c0ec1.IT BndT_Ns_001.SegItab_Ns_5c0ec1.IT_sound BF NX0 BR XSTEP F0 PSS plan 277500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twDc.

Module LibSegNs_twDd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_6d2d03.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_6d2d03.IT.
Definition ENDS : list Z := [278968].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##428=<+$2-130$3$4$<=$<>$<?$29+$2#48#$=3$78^#8#:<7230489>80000$=6$=7$=8$=9+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#38,8$24!$2#40,8$26!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42808#$29##8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?8#<,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8,$23#10#30'$78#1#7???????"%pstring).
Definition ss0 : sym_state := SS 278772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96); ((EVar 42), (0), ELit 64); ((EVar 35), (0), ELit 64); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96); ((EVar 42), (0), 64); ((EVar 35), (0), 64); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#441;8#5=#441;8,20##428?8+$2-140$3$4+$2-70&4$26+&4$24@^-7-538=<?;76180000$78+&4@^-7-538=<?;76180000$78@#89>80000$78&6@#8:<72304$78#20$26@#89>80000$78@#89>80000$78#????????+$2#38+$2-78#8+$2-?8+$2#48+$2#48+$26+@-1&4$24@^-7-538=<?;76180000$78+@-1&4@^-7-538=<?;76180000$78@#89>80000$78@-1&6@#8:<72304$78#20+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78+&4$24@^-7-538=<?;76180000$78+&4@^-7-538=<?;76180000$78@#89>80000$78&6@#8:<72304$78#20&4@^-7-538=<?;76180000$78@#89>80000$78#+$24@^#7#538=<?;76180000$78,,79!$2#40,8+$26+@-1&4$24@^-7-538=<?;76180000$78+@-1&4@^-7-538=<?;76180000$78@#89>80000$78@-1&6@#8:<72304$78#20!$2#38,8+$24@^#7#538=<?;76180000$78!$2-140,8+$2#48!$2-138,8$29!$2-?8,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48#$29##8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8,$23#10#30'$78#1#7???????,?;!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 278968 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_6d2d03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_6d2d03.IT BndT_Ns_001.SegItab_Ns_6d2d03.IT_sound BF NX0 BR XSTEP F0 PSS plan 278772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twDd.

Module LibSegNs_twDe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7b5ef1.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7b5ef1.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##428?8+$2-140$3$4+$2-70$<>$26$=0$=1#????????+$2#38+$2-78#8+$2-?8+$2#48+$2#48$=9+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78$7:$>5#$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7;'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????!$2-140,8+$2#48!$2-138,8$29!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48#$29##8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8,$23#10#30!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##"%pstring).
Definition ss0 : sym_state := SS 278968 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-480), ELit 480); ((EVar 2), (8), ELit 96); ((EVar 42), (0), ELit 64); ((EVar 35), (0), ELit 64); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-480), 480); ((EVar 2), (8), 96); ((EVar 42), (0), 64); ((EVar 35), (0), 64); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#63=<4#5;#43860,20##44290+$2-170$3$4+$2-70$<>$26+$2#28#+$2#28&9$2;#?=#1+$2#38+$2#38$79+$2#48$=9+$2#48$3;+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$7:$>5#$>7,,7;!$2#30,8#1!$2-148,8+$2#48!$2-140,8+$2#28!$2-138,8#42950!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#28,1&9$2;#?=!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8,$23#10#30!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##,?;!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ce2 : expr := EVar 121.
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#63=<4#5=#63=<4,20##429:0+$2-130$3$4+$2-70$<>$26+$2#28+$2#48$23#40#+$2#38+$2#30$79+$2#48$=9+$2#48$3;+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$7:$>5#$>7,,7<!$2#28,1&8&9$2;#?=$3;!$2#30,8#'$79##!$2-148,8+$2#48!$2-140,8+$2#28!$2-138,8#42950!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8,$23#10#30!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##,?;!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#63=<4#5=#63=<4,20##429:0+$2-130$3$4+$2-70$<>$26+$2#28+$2#48$23#40#1+$2#38+$2#38$79+$2#48$=9+$2#48$3;+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$7:$>5#$>7,,7<!$2#28,1&8&9$2;#?=$3;'$79#1^#8#:<7230489>7????!$2#30,8#1!$2-148,8+$2#48!$2-140,8+$2#28!$2-138,8#42950!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$23#1000#7??????00000($23##40)##10000#;6<<0$23##40)$23##40$29##40)$23##40$2:##40)$2-1>0#248$23##40'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2-1=8,8#1!$2-1=0,8&9$37#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$2:!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$23#,8$24!$23#8,8$26!$2-;0,8$23!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38,$2-1>0#8,$23#10#30!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##,?;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7b5ef1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278968 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7b5ef1.IT BndT_Ns_001.SegItab_Ns_7b5ef1.IT_sound BF NX0 BR XSTEP F0 PSS plan 278968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twDe.

Module LibSegNs_twDf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_a8b108.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_a8b108.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-130$3$4$<=$<>$<?+$2#28+$2#48$=2$=3$=4$=5$=6$=7$=8$=9+$2#48$3<+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5<'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????'$79#^#8#:<7230489>7????'&4$26$7:##!$2#28,1&8&9$2;#?=$3;!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#50,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38!$2#38,8$79!$2#40,8#!$2#30,8$39,$2-1>0#;0"%pstring).
Definition ss0 : sym_state := SS 272800 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#63=<4#5=#63=<4,20##429<0+$2-130$3$4$<=$<>$<?+$2#28+$2#48$2:#40$=4$=5$=6$=7$=8$=9+$2#48$3<+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$>4$>5$>6$>7,,5<'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$2:#1000#7??????00000($2:##40)##10000#;6<<0$2:##40)$2:##40$29##40)$2-1>0#248$2:##40'$37##??'&9$37#1#1#1'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????'$79#^#8#:<7230489>7????'&4$26$7:##!$2#28,1&8&9$2;#?=$3;!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#50,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2:#,8$24!$2:#8,8$26!$2-90,8$2:!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30,$2:#10#30!$2-<8,1$38!$2#38,8$79!$2#40,8#!$2#30,8$39,$2-1>0#;0,?;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_a8b108.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 272800 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_a8b108.IT BndT_Ns_001.SegItab_Ns_a8b108.IT_sound BF NX0 BR XSTEP F0 PSS plan 272800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twDf.

Module LibSegNs_twDg.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-130$3$4$<=$<>$<?+$2#28+$2#48$=2$=3$=4$=5$=6$=7$=8$=9+$2#48$3<+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",53'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$37##??'&9$37#1#1#1'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????'$79#^#8#:<7230489>7????'&4$26$7:##!$2#28,1&8&9$2;#?=$3;!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#50,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30!$2-<8,1$38!$2#38,8$79!$2#40,8#!$2#30,8$39,$2-1>0#;0"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#42:18#5=#42:18,20#$28$2$3$4$<=$<>$<?$8$9#$=3$=4$=5$=6$=7$=8$=9$12$13$14$15$16$17$18$19$1:$1;$>4$>5$>6$>7,,53'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1#1#1'$2;##??'&9$2;#1##'$29#1000#7??????00000($29##40)$2-1>0#248$29##40)##10000#;6<<0$29##40'$32##??'$33##??'$34##??'$35##??'$26#1#40000000'$37##??'&9$37#1#1#1'$38##??'&9$38#1#1#1'$3;##2'$78#1#7???????'$79#^#8#:<7230489>7????'&4$26$7:##!$2#28,1&8&9$2;#?=$3;!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$29#,8$78!$2-?8,8$78!$2-110,8+$2#28!$2-118,8$3;!$2-120,8&6&5#&9$25#2#1!$2#50,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;8,8#8!$2-<0,8#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9$37#?=!$2-98,8#8!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#58,8#8!$2#60,8$29!$29#8,8$26,$29#10#30!$2-<8,1$38!$2#38,8$79!$2#40,8#!$2#30,8$39,$2-1>0#;0,?;!"%pstring).
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
End LibSegNs_twDg.

Module LibSegNs_twIa.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_88783e.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_88783e.IT.
Definition ENDS : list Z := [278528].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#48+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#1>0($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#28,1$2;!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1$25!$2#50,8#2!$2#58,8$24!$2#60,8$26'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##!$2-88,1$32'$32##??!$2-:8,1$33'$33##??!$2-<8,1$34'$34##??!$2->8,1$35'$35##??"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",5!!,5#42:18#44000#;>8;0#63=<4#44000!$!!,5#42:18#44000#;>8;0#63=<4#44000!#!!,5#42:18#44000#;>8;0#63=<4#44000#5=#44000,20##428=<+$2-130$3$4$61$62$63+$2#58+$2#48+$2#48$26$24^#8#:<7230489>80000$68$69$6:$6;+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78$6<$6=$6>$6?,,5:!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2#38,8$24!$2#40,8$26!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42808#$2#58#8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0,$2-1>0#8,$2-130#8,$2-?8#<,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7($2#8#60!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#60,8$26'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??,70!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 278528 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_88783e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_88783e.IT BndT_Ns_001.SegItab_Ns_88783e.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twIa.

Module LibSegNs_twIb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_6d2d03.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_6d2d03.IT.
Definition ENDS : list Z := [278968].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##428=<+$2-130$3$4$<=$<>$<?+$2#58+$2#48#$=3$78^#8#:<7230489>80000$=6$=7$=8$=9+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5;'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2#38,8$24!$2#40,8$26!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48!$2-140,8&6&5#&9$25#2#1!$2-138,8#42808#$2#58#8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#8,$2-?8#<,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#60,8$26'$78#1#7???????"%pstring).
Definition ss0 : sym_state := SS 278772 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#441;8#5=#441;8,20##428?8+$2-140$3$4+$2-70&4$26+&4$24@^-7-538=<?;76180000$78+&4@^-7-538=<?;76180000$78@#89>80000$78&6@#8:<72304$78#20$26@#89>80000$78@#89>80000$78#????????+$2#38+$2-78#8+$2-?8+$2#48+$2#48+$26+@-1&4$24@^-7-538=<?;76180000$78+@-1&4@^-7-538=<?;76180000$78@#89>80000$78@-1&6@#8:<72304$78#20+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78+&4$24@^-7-538=<?;76180000$78+&4@^-7-538=<?;76180000$78@#89>80000$78&6@#8:<72304$78#20&4@^-7-538=<?;76180000$78@#89>80000$78#+$24@^#7#538=<?;76180000$78,,5<!$2#40,8+$26+@-1&4$24@^-7-538=<?;76180000$78+@-1&4@^-7-538=<?;76180000$78@#89>80000$78@-1&6@#8:<72304$78#20!$2#38,8+$24@^#7#538=<?;76180000$78!$2-140,8+$2#48!$2-138,8+$2#58!$2-?8,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48#$2#58#8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#60,8$26'$78#1#7???????,?;!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 278968 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_6d2d03.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_6d2d03.IT BndT_Ns_001.SegItab_Ns_6d2d03.IT_sound BF NX0 BR XSTEP F0 PSS plan 278772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twIb.

Module LibSegNs_twIc.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7b5ef1.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7b5ef1.IT.
Definition ENDS : list Z := [272920].
Definition STOPS1 : list Z := [272920; 278528; 780464; 409028] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##428?8+$2-140$3$4+$2-70$<>$26$=0$=1#????????+$2#38+$2-78#8+$2-?8+$2#48+$2#48$=9+$2#48^#?#??????????????8+$2-78#1#^#8#:<7230489>80000+$2#38+$2#40#+$2-78$7:$>5#$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",5>'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??'$78#1#7???????!$2-140,8+$2#48!$2-138,8+$2#58!$2-?8,8$78!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2#28,1&9$2;#?=!$2#30,8#2!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2-148,8+$2#48#$2#58#8!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#48,1$25!$2#60,8$26!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##"%pstring).
Definition ss0 : sym_state := SS 278968 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#42:18#5;#43860,20##44290+$2-170$3$4+$2-70$<>$26+$2#28#+$2#28&9$2;#?=#1+$2#38+$2#38$79+$2#48$=9+$2#48&9$25#2+$2-78#1#^#8#:<7230489>80000+$2#38+$2#38#+$2-78$7:$>5#$>7,,5>!$2#30,8#1!$2-148,8+$2#48!$2-140,8+$2#28!$2-138,8#42950!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#58,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??'$78#1#7???????!$2-?8,8$78!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2#28,1&9$2;#?=!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#60,8$26!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##,?;!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ce2 : expr := EVar 121.
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#42:18#5=#42:18,20#$28$2$3$4+$2-70$<>$26$8$9#&9$2;#?=#+$2#38+$2#30$79+$2#48$=9$12$13$14$15$16$17$18$19$1:$1;$7:$>5#$>7,,5?!$2#28,1&8&9$2;#?=&9$25#2!$2#30,8#'$79##!$2-148,8+$2#48!$2-140,8+$2#28!$2-138,8#42950!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#58,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??'$78#1#7???????!$2-?8,8$78!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#60,8$26!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##,?;!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#42:18#44000#;>8;0#63=<4#42:18#5=#42:18,20#$28$2$3$4+$2-70$<>$26$8$9#&9$2;#?=#1+$2#38+$2#38$79+$2#48$=9$12$13$14$15$16$17$18$19$1:$1;$7:$>5#$>7,,5?!$2#28,1&8&9$2;#?=&9$25#2'$79#1^#8#:<7230489>7????!$2#30,8#1!$2-148,8+$2#48!$2-140,8+$2#28!$2-138,8#42950!$2#48,1&8&9$25#?=@#2&6&5#&9$25#2#1!$2#58,8$78'$2#7???7?8001>0#800000000000&$2#10($2-1>0#1>0%#10000#<6<<0($2#8#60'$25##??'&9$25#1##'$26#1#40000000'$2;##??'&9$2;#1##'$32##??'$33##??'$34##??'$35##??'$78#1#7???????!$2-?8,8$78!$2-110,8+$2#28!$2-118,8&9$25#2!$2-120,8&6&5#&9$25#2#1!$2-1=8,8#1!$2-1=0,8&9+@#4&6$33#2&9$25#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#2!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#2!$2-178,8$26!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#2!$2-150,8+$2#48!$2#50,8#1!$2-1:0,8+$2-78!$2-198,8#2!$2-190,8#2!$2-188,8#1!$2-108,8+$2#58!$2-128,8#!$2-><,4#!$2-=0,8#!$2-=8,8^#8#:<7230489>80000!$2->0,8#1!$2->8,1@#4&6$35#2!$2-;0,8$26!$2-;8,8$24!$2-<0,8#2!$2-<8,1@#4&6$34#2!$2-100,8#1!$2-88,1@#4&6$32#2!$2-:8,1&9+@#4&6$33#2&9$25#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8^#8#:<7230489>80000!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#8,$2-?0#4,$2->7#7,$2-<7#7,$2-:7#7,$2-87#7!$2#8,1#!$2#10,8#1!$2#18,8^#8#:<7230489>80000!$2#20,8#!$2#60,8$26!$2#38,8$79!$2#40,8#'$79#^#8#:<7230489>7????'&4$26$7:##,?;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7b5ef1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 278968 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7b5ef1.IT BndT_Ns_001.SegItab_Ns_7b5ef1.IT_sound BF NX0 BR XSTEP F0 PSS plan 278968 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twIc.

Module LibSegNs_twhD0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_56547e.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_56547e.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1#1#1!$22#8,8#2!$22#10,8#8!$22#18,8$27'$27#1000#7??????00000!$27#,8$24!$27#8,8$26)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0#5=#;>8;0,20##43;?<+$2-100$3$4$5$6$7$22+$2-78#40#+$2-78$=$>$?$10$11#2$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2?!$2-60,8#!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2->0,8$12!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<84!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1<0,$2-<0#48,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1#1#1!$22#8,8#2!$22#10,8#8!$22#18,8$27'$27#1000#7??????00000!$27#,8$24!$27#8,8$26)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_56547e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289856 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_56547e.IT BndT_Ns_001.SegItab_Ns_56547e.IT_sound BF NX0 BR XSTEP F0 PSS plan 289856 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twhD0.

Module LibSegNs_twhD1L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_57e41b.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_57e41b.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-100$3$4$<=$<>$<?$22+$2-78$29$=3$=4$=5$=6$=7$=8$=9#2$13$14$15$16$17$18$19$1:$1;$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1#1#1'$27#1000#7??????00000)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-60,8#!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2->0,8$12!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<84!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-100#20,$2-<0#48,$2-77#7!$22#,1$25!$22#8,8#2!$22#10,8#8!$22#18,8$27!$27#,8$24!$27#8,8$26,$2-2:0#1:0'$29#1000#7??????00000($29##40)$2-2:0#2:0$29##40)##10000#;6<<0$29##40)$29##40$22##20)$29##40$2=##18)$29##40$27##10,$29##40!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20)$29##40$2?##20"%pstring).
Definition ss0 : sym_state := SS 277500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,6#46>88#;>8;0#63=<4#42450#;9=7<#42450!#!!,6#46>88#;>8;0#63=<4#42450#;9=7<#42450#5=#42450,20##46=04+$2-<0$3$4$?<$?=$?>$2=$22+$2-78+$2-;8+$2-78+$2-98#1$104$105$106+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$107$108$109$10:,,53!$2-:0,8#!$2-:8,8^#8#:<7230489>80000!$2-;0,8#1!$2-;8,1#!$2-80,8#!$2-88,8#!$2-90,8#!$2-98,1#!$29#,8$24!$29#8,8$26!$2-60,8$29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1#1#1'$27#1000#7??????00000)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2->0,8$12!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<84!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-100#20,$2-<0#8,$2-;7#7,$2-97#7,$2-77#7!$22#,1$25!$22#8,8#2!$22#10,8#8!$22#18,8$27!$27#,8$24!$27#8,8$26,$2-2:0#1:0'$29#1000#7??????00000($29##40)$2-2:0#2:0$29##40)##10000#;6<<0$29##40)$29##40$22##20)$29##40$2=##18)$29##40$27##10,$29#10#30!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20)$29##40$2?##20,10;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_57e41b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_57e41b.IT BndT_Ns_001.SegItab_Ns_57e41b.IT_sound BF NX0 BR XSTEP F0 PSS plan 277500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twhD1L.

Module LibSegNs_twhD1M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_dff627.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_dff627.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-100$3$4$<=$<>$<?$22+$2-78$29$=3$=4$=5$=6$=7$=8$=9#2$13$14$15$16$17$18$19$1:$1;$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",47'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1#1#1'$27#1000#7??????00000)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-60,8#!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2->0,8$12!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<84!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-100#20,$2-<0#48,$2-77#7!$22#,1$25!$22#8,8#2!$22#10,8#8!$22#18,8$27!$27#,8$24!$27#8,8$26,$2-2:0#1:0'$29#1000#7??????00000($29##40)$2-2:0#2:0$29##40)##10000#;6<<0$29##40)$29##40$22##20)$29##40$2=##18)$29##40$27##10,$29##40!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#2='&9$2>#1#1#1'+&9$2>-2-1#19#2;'$2?#1000#7??????00000,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:)$29##40$2?##1:"%pstring).
Definition ss0 : sym_state := SS 277500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0!#!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0#5=#;>8;0,20##660>0+$2-110$3$4$?<$?=$?>$2=#2?#30$2>#1#16$103$104$105$106#2#30#+@#2&6$2>#1-1#1+@#2&6$2>#1-1$18$19$1:$1;$107$108$109$10:,,4=!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#2!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<:8!$29#,8$24!$29#8,8$26!$2-60,8$29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1#1#1'$27#1000#7??????00000)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-<0#48,$2-77#7!$22#,1$25!$22#8,8#2!$22#10,8#8!$22#18,8$27!$27#,8$24!$27#8,8$26,$2-2:0#198'$29#1000#7??????00000($29##40)$2-2:0#2:0$29##40)##10000#;6<<0$29##40)$29##40$22##20)$29##40$2=##18)$29##40$27##10,$29#10#30!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#1;#2='&9$2>#1#1#1'+&9$2>-2-1#19#2;'$2?#1000#7??????00000,$2?##1:)$2?##1:$2=##18)$2?##1:$22##20)$2-2:0#2:0$2?##1:)$29##40$2?##1:,10;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_dff627.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_dff627.IT BndT_Ns_002.SegItab_Ns_dff627.IT_sound BF NX0 BR XSTEP F0 PSS plan 277500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twhD1M.

Module LibSegNs_twhD1S.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_dff627.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_dff627.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 251.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$<9+$2-100$3$4$<=$<>$<?$22+$2-78$29$=3$=4$=5$=6$=7$=8$=9#2$13$14$15$16$17$18$19$1:$1;$>4$>5$>6$>7"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",3<'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1#1#1'$27#1000#7??????00000)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-60,8#!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2->0,8$12!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<84!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-100#20,$2-<0#48,$2-77#7!$22#,1$25!$22#8,8#2!$22#10,8#8!$22#18,8$27!$27#,8$24!$27#8,8$26,$2-2:0#1:0'$29#1000#7??????00000($29##40)$2-2:0#2:0$29##40)##10000#;6<<0$29##40)$29##40$22##20)$29##40$2=##18)$29##40$27##10,$29##40!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##"%pstring).
Definition ss0 : sym_state := SS 277500 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-672), ELit 672); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-672), 672); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0!#!!,6#46>88#;>8;0#63=<4#42450#;9=7<#;>8;0#5=#;>8;0,20##660>0+$2-110$3$4$?<$?=$?>$2=#2?#30@#100000000000000$31##16$103$104$105$106#2#30&6@#100000000000000$31#39#16#+@#2&6$31#1-1$18$19$1:$1;$107$108$109$10:,,42!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8#2!$2-=8,8$22!$2-=0,8$2=!$2-<8,8#46<:8!$29#,8$24!$29#8,8$26!$2-60,8$29'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20'$25##??'&9$25#1#1#1'$27#1000#7??????00000)$2-2:0#2:0$27##10)$27##10$22##20)$27##10$2=##18'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2-68,8#8!$2-70,8#2!$2-78,1&8&9$25#2&9+@#2&6$32#1#1#?=!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-<0#48,$2-77#7!$22#,1$25!$22#8,8#2!$22#10,8#8!$22#18,8$27!$27#,8$24!$27#8,8$26,$2-2:0#198'$29#1000#7??????00000($29##40)$2-2:0#2:0$29##40)##10000#;6<<0$29##40)$29##40$22##20)$29##40$2=##18)$29##40$27##10,$29#10#30!$2=#,1#!$2=#,8$31'&9$31#1##'&9$31#??##,10;!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_dff627.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 277500 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_dff627.IT BndT_Ns_002.SegItab_Ns_dff627.IT_sound BF NX0 BR XSTEP F0 PSS plan 277500 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_twhD1S.

Module LibSegNs_twhL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_ad1669.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_ad1669.IT.
Definition ENDS : list Z := [271440].
Definition STOPS1 : list Z := [290440; 780464; 409028; 271440; 761212] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; EVar 45; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#2:0!$2-78,1$32'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#2!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#46>88#;>8;0#63=<4#42450#;9=7<#42450#5=#42450,20##46=04+$2-<0$3$4$5$6$7$2=$22+$2-78+$2-;8+$2-78+$2-98#1$?$10$11+$2-88#:^#<#<<<<<<<<<<<<<<=#12$16$17$18$19$1:$1;$1<$1=$1>$1?,,3<!$2-:0,8#!$2-:8,8^#8#:<7230489>80000!$2-;0,8#1!$2-;8,1#!$2-80,8#!$2-88,8#!$2-90,8#!$2-98,1#!$2-60,8$26!$2-68,8$24!$2-70,8#2!$2-78,1+@#4&6$32#2&9$25#2!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8002:0#800000000000&$2#10($2-2:0#2:0%#10000#<6<<0,$2-2:0#1>8,$2-;7#7,$2-97#7,$2-77#7'$32##??'$22#7???7?8002:0#7?????????>0&$22#8)$2-2:0#2:0$22##20!$22#,1$25'$25##??'&9$25#1##!$22#8,8#2!$22#10,8$24!$22#18,8$26'$2=#7???7?8002:0#7?????????>8&$2=#8)$2-2:0#2:0$2=##18($2=##18)$22##20$2=##18!$2=#,1$31'$31##??'&9$31#1#1#1!$2=#,8$2>!$2=#8,8#!$2=#10,8$2?'$2>#2?#10000001'+&9$2>-2-1#2=#???????'$2?#1000#7??????00000($2?##20,$2?##20)$2?##20$2=##18)$2?##20$22##20)$2-2:0#2:0$2?##20,50!"%pstring).
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
End LibSegNs_twhL.

End BndP_Ns_081.
