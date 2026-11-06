(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_141.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_141 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32L3ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu32M3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64A3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64L3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141ALibSegNa_antbu64M3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_asyB3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_atoB3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_avzA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacB3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qacC3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_141=LibSegNa_qrcA3ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNa_antbu32L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815800, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [815968].
Definition STOPS1 : list Z := [815968] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;#1$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 815932 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<7360#<7360#5=#<7360,20#$2<$2$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 815968 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu32L.

Module LibSegNa_antbu32M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815800, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;$23$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#4'$24#1000#7??????????>'+$2@-1$24#2>#30!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 815932 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<733<+$2-30$3$4$5$6$7$;+$23-1$29+$2-29$39$=$>$?$10$11+$24#1+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#4'$24#1000#7??????????>'+$2@-1$24#2>#30!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815932 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815932 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu32M.

Module LibSegNa_antbu64A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815980, 59%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 815980 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<7428+$2-40$3$4$5$6$7$;#8$29+$2-29&8+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8&9&6$:#28#??00&6$:#38@#10000000000&9$:#??00+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8@#1000000&9$:#??0000@#100000000%6$:#18@#1000000&9$:#??0000$11+$2-38+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-29,1[,,1&8&8+@#100000000000000$:@#10000000000&9$:#??00&8@#1000000&9$:#??0000@#100000000%6$:#18&8+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8&9&6$:#28#??00&6$:#38!$2-38,8&8&8+@#100000000000000$:@#10000000000&9$:#??00&8@#1000000&9$:#??0000@#100000000%6$:#18&8+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8&9&6$:#28#??00&6$:#38!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815980 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815980 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu64A.

Module LibSegNa_antbu64L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815980, 59%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [816204].
Definition STOPS1 : list Z := [816204] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$;#1$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 816168 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<744<#<744<#5=#<744<,20#$2<$2$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 816204 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 816168 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 816168 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu64L.

Module LibSegNa_antbu64M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815980, 59%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$;$23$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8'$23#2#8'$24#1000#7??????????>'+$2@-1$24#32#38!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 816168 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<7428+$2-40$3$4$5$6$7$;+$23-1$29+$2-29$39$=$>$?$10$11+$24#1+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8'$23#2#8'$24#1000#7??????????>'+$2@-1$24#32#38!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 816168 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 816168 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu64M.

Module LibSegNa_asyA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(1018160, 20%nat) ; (874144, 20%nat) ; (874224, 5%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1018184].
Definition STOPS1 : list Z := [1018184] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KWord (SA (ELit 0) 6890288) 1 (ELit 1)].
Definition ss0 : sym_state := SS 1018160 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?8948#?8948#5=#?8948,20#$1$2$3$4$5$6$7$8$9#15;508$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1!##692330,1#1,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1018184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1018160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1018160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_asyA.

Module LibSegNa_asyB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(1018160, 20%nat) ; (874144, 20%nat) ; (874224, 5%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [1018184].
Definition STOPS1 : list Z := [1018184] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487184 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KImg 6890288 6890290;
   KWr (SA (ELit 0) 6890288) (ELit 2)].
Definition ss0 : sym_state := SS 1018160 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16); ((ELit 0), (6890288), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16); ((ELit 0), (6890288), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#?8948#?8948#5=#?8948,20#$1$2$3$4$5$6$7$8$9#15;508#1#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7!##692331,1#1!##692330,1#1!$2-8,8$1'$2#7???7?801010#800000000000&$2#10($2-10#10(##692330#2,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1018184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1018160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 1018160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_asyB.

Module LibSegNa_atoA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(816880, 32%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [816916; 816968].
Definition STOPS1 : list Z := [816916; 816968; 816988] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 34); (EVar 33); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487296 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-16)) (ELit 16);
   KRange (EVar 34) 0 140737488355328;
   KRange (EVar 33) 0 31].
Definition ss0 : sym_state := SS 816880 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#<7714#<7748#<775<#<7714#<7748#5;#<76?8,20#$1+$2-10$3$4$5$6$7$8$9$22$21$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10($2-10#10'$22##800000000000'$21##1?,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",2!!,5#<7714#<7748#<775<#<7714#<7748!!,5#<7714#<7748#<775<#<7714#<7748#5=#<7748,20#$1+$2-10$3$4$5$6$7$8$9$22#16$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$21##1#1#1!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10($2-10#10'$22##800000000000'$21##1?,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,5#<7714#<7748#<775<#<7714#<7748#5=#<7714,20#$1+$2-10$3$4$5$6$7$8$9$22$21+&6$22#3#7???8000$23&6$22#3$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$21##1##!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10($2-10#10'$22##800000000000'$21##1?,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 1)) (SGA.mkplan (fst ex4) (SGP.PEnd 0))).
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

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s4).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s4).
Definition ps0 : SR.post_spec := SR.PS 816916 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 816968 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 816880 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 816880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_atoA.

Module LibSegNa_atoB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(816880, 32%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [823824; 823824].
Definition STOPS1 : list Z := [823824] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-10$3$4$5$6$7$8$9$22$21$20$23$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10'$22#1000#7???????????'$21#1#1?!$22#,1$25'$25##??"%pstring).
Definition ss0 : sym_state := SS 816924 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<9210#<9210#<9210#5;#<7724,20#$1+$2-10$3$4$5$6$7$8$9$22$21$25$23#2=$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10'$22#1000#7???????????'$21#1#1?!$22#,1$25'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<9210#<9210#<9210#5=#<9210,20##<7748+$2-10$3$4$5$6$7$8$9+$22#1+$21-1#1$23+$2-9$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$25#2=#1#1#1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10'$22#1000#7???????????'$21#1#1?!$22#,1$25'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<9210#<9210#<9210#5=#<9210,20##<7748+$2-10$3$4$5$6$7$8$9$22$21#$23+$2-:$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'&4&1$25#2=#1##%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801080#800000000000&$2#10'$22#1000#7???????????'$21#1#1?!$22#,1$25'$25##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 823824 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 823824 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 816924 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 816924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_atoB.

Module LibSegNa_avzA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(873428, 39%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [873584; 791888; 873560].
Definition STOPS1 : list Z := [873584; 791888; 873560] ++ ENDS.
Definition NX0 : nat := 70.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 37; EVar 43; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$25#6;6000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-10#10$25##18!$25#,8$28!$25#8,8+$28$29'$28##800000000000'$29##8000000'$2;##8000000"%pstring).
Definition ss0 : sym_state := SS 873428 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-16), ELit 16); ((EVar 37), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-16), 16); ((EVar 37), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=5470#<1550#=5458#=5470#<1550#=5458#5;#=5418,20#$1+$2-10$3$4$5$6$7$8$9$25$2;+$25#8$29+&6+$25#8#3#7???8000$28$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$25#6;6000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-10#10$25##18!$25#,8$28!$25#8,8+$28$29'$28##800000000000'$29##8000000'$2;##8000000,46!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=5470#<1550#=5458#=5470#<1550#=5458#5=#=5470,20#$1$2$3$4$5$6$7$8$9$25+@-1$29$2;+$25#8$29+&6+$25#8#3#7???8000$28$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'&4$29$2;#1#1!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$25#6;6000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-10#10$25##18!$25#,8$28!$25#8,8+$28$29'$28##800000000000'$29##8000000'$2;##8000000,46!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=5470#<1550#=5458#=5470#<1550#=5458#5;#=542<,20#$1+$2-10$3$4$5$6$7$8$9$25$2;+$25#8$29+&6+$25#8#3#7???8000$28$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'&4$29$2;##!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$25#6;6000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-10#10$25##18!$25#,8$28!$25#8,8+$28$29'$28##800000000000'$29##8000000'$2;##8000000,46!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=5470#<1550#=5458#=5470#<1550#=5458#5=#<1550,20#$1$2$3$4$5$6$7$8$9$25$29+$25#8$29#$28$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$25#8,8+$28$2;'&4$2;$29#1#1'&4$29$2;##!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$25#6;6000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-10#10$25##18!$25#,8$28'$28##800000000000'$29##8000000'$2;##8000000,46!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#=5470#<1550#=5458#=5470#<1550#=5458#5=#=5458,20#$1$2$3$4$5$6$7$8$9$25$2;+$25#8$29+&6+$25#8#3#7???8000$28$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4$2;$29##'&4$29$2;##!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$25#6;6000#7?????????>8&$25#8)##7???7000#100000001000$25##18#&6$25#3#7???8000#3($25##18)$2-10#10$25##18!$25#,8$28!$25#8,8+$28$29'$28##800000000000'$29##8000000'$2;##8000000,46!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PEnd 2))))).
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
Definition ps0 : SR.post_spec := SR.PS 873584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 791888 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 873560 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 873428 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 873428 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avzA.

Module LibSegNa_qacA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(847396, 60%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280; 847556] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 36); (EVar 37); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?801050#800000000000&$2#10($2-50#50%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60)$2-50#50$24##60#&6$24#3#7???8000#3($24##18"%pstring).
Definition ss0 : sym_state := SS 847396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 36), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 36), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#7?058#<>><4#7?058#5=#7?058,20##<>><4+$2-50$3$4$5$6$7$24+$24#18+$24#18##48$=$>$?$10$11$12+$24#30+$24#48#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#10,8$25!$24#8,8#151408!$24#,8#150=88!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801050#800000000000&$2#10($2-50#50%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60)$2-50#50$24##60#&6$24#3#7???8000#3($24##18,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 847396 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 847396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qacA.

Module LibSegNa_qacB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(847396, 60%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [754920].
Definition STOPS1 : list Z := [754920; 847580] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13+$24#48#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487248 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-72)) (ELit 16)].
Definition ss0 : sym_state := SS 847556 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-68), ELit 4); ((EVar 2), (-64), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-68), 4); ((EVar 2), (-64), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;84>8#<>>=<#;84>8#5=#;84>8,20##<>>=<+$2-50$3$4$5$6$7$24$9+$24#48+$2-40+$2-44$=$>$?$10$11$12$13+$24#48#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,5!$2-44,4#!$2-40,4#'$2#7???7?801050#800000000000&$2#10($2-48#10,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 754920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 847556 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 847556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qacB.

Module LibSegNa_qacC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(847396, 60%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [847612].
Definition STOPS1 : list Z := [847612] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?801050#800000000000&$2#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31"%pstring).
Definition ss0 : sym_state := SS 847580 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<>>?<#<>>?<#5=#<>>?<,20#$2;$2$3$4$5$6$7$2<$2=$:$;$<$=$>$?$10$11$2>$2?$30$31$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?801050#800000000000&$2#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 847612 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 847580 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 847580 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qacC.

Module LibSegNa_qrcA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(720556, 40%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [846716].
Definition STOPS1 : list Z := [846716; 720620] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487216 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1)].
Definition ss0 : sym_state := SS 720556 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<>;7<#:?>><#<>;7<#5=#<>;7<,20##:?>><+$2-30$3$4$5$6$7$:$9$:$;$=$>$>$?$10$11$>$<#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,<!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801030#800000000000&$2#10($2-30#30%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 846716 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720556 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 720556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrcA.

End BndP_Na_141.
Module BndP_Na_142.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_142 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcB3ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qrcC3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruA3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_qruB3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142>LibSegNa_qvfA23ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_142=LibSegNa_vfpC3ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNa_qrcB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(720556, 40%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [847396].
Definition STOPS1 : list Z := [847396; 720640] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$21$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 720620 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<>>24#:??00#<>>24#5=#<>>24,20##:??00+$2-30$3$4$5$6$7$21+$21#190+$21#190$13$12$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 847396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720620 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 720620 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrcB.

Module LibSegNa_qrcC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(720556, 40%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [720692].
Definition STOPS1 : list Z := [720692] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$21+$21#190$:$;$<$=$>$?$10$11$12$13#7???8000$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?801030#800000000000&$2#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-30#30$21##1?8#&6+$21#1?0#3#7???8000#1($21#1?0#8"%pstring).
Definition ss0 : sym_state := SS 720640 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (496), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (496), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:??34#:??34#5=#:??34,20#$2;$2$3$4$5$6$7$2<$2=+$21#1?0#$<$=$>$?$10$11$2>$2?$30$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!$21#1?0,8+$21#190'$2#7???7?801030#800000000000&$2#10!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-30#30$21##1?8#&6+$21#1?0#3#7???8000#1($21#1?0#8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 720640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrcC.

Module LibSegNa_qruA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(837920, 46%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [830872].
Definition STOPS1 : list Z := [830872; 839736; 840492; 991168; 838056] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 34); (EVar 33); (ELit 0); (ELit 0); EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 837920 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-24), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-24), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:=98#<=038#<=32<#?1?<0#<<9:8#<:=98#5=#<:=98,20##<<998+$2-40$3$4$5$6$7$21#$21$21##$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 830872 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 837920 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 837920 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qruA.

Module LibSegNa_qruB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(837920, 46%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [838056].
Definition STOPS1 : list Z := [838056] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$21#$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWord (SA (EVar 2) (-8)) 8 (EVar 53);
   KWord (SA (EVar 2) (-16)) 8 (EVar 54);
   KWord (SA (EVar 2) (-24)) 8 (EVar 55)].
Definition ss0 : sym_state := SS 838040 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<<9:8#<<9:8#5=#<<9:8,20#$35$2$3$4$5$6$7$36$37$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?801040#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 838056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 838040 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 838040 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qruB.

Module LibSegNa_qvfA2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(732160, 29%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [796868].
Definition STOPS1 : list Z := [796868] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 36); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11%#10000#158000!##15?:78,8#7???8000'$2#7???7?801010#800000000000&$2#10($2-10#10'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60)$2-10#10$24##60#&6+$24#10#3#7???8000#1!$24#10,8$26'$26#6;6000#7?????????<8)##7???7000#100000001000$26##8)$2-10#10$26##8#&6$26#3#7???8000#1!$26#,8#151130###8002222=#1"%pstring).
Definition ss0 : sym_state := SS 732160 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<28<4#<28<4#5=#<28<4,20#$1$2$3$4$5#<28<4$7$8$9$26#151168##2:22=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-8,8$1%#10000#158000!##15?:78,8#7???8000'$2#7???7?801010#800000000000&$2#10($2-10#10'$24#6;6000#7?????????:0&$24#8)##7???7000#100000001000$24##60)$2-10#10$24##60#&6+$24#10#3#7???8000#1!$24#10,8$26'$26#6;6000#7?????????<8)##7???7000#100000001000$26##8)$2-10#10$26##8#&6$26#3#7???8000#1!$26#,8#151130###8002222=#1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 796868 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 732160 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 732160 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qvfA2.

Module LibSegNa_vfpC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(452984, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [453116].
Definition STOPS1 : list Z := [453116] ++ ENDS.
Definition NX0 : nat := 140.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$29+$2-30$2;$2<$2=$2>$2?$30$31$25$33$34$35$36$37$38$39$3:$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#10007???8000#800000000000($2-1000#1000%#10000#158000!$2-8,8$1!$2-10,8$8!$2-18,8$9!$2-20,8$12,$2-1000#?=0"%pstring).
Definition ss0 : sym_state := SS 453096 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-4096), ELit 4096)].
Definition F0L : list SR.region := [(EVar 2, (-4096), 4096)].
Definition BF : nat := 200000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6>9?<#6>9?<#5=#6>9?<,20#$1$2$2;$2<$2=$2>$2?$8$9$25$33$34$35$36$37$38$39$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#10007???8000#800000000000($2-1000#1000%#10000#158000!$2-8,8$1!$2-10,8$8!$2-18,8$9!$2-20,8$12,$2-1000#?=0,8<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 453116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 453096 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 453096 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_vfpC.

End BndP_Na_142.
Module BndP_Na_140.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_140 () := "C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01126LibSym7itab_ofC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbf64M3ITRC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16A3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16L3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi16M3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32A3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32L3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi32M3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64A3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64L3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbi64M3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16A3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16L3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu16M3ITRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_140ALibSegNa_antbu32A3ITRC1?~~~~~~~~~~~~~~~".

Module LibSegNa_antbf64M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(816400, 60%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$2;$23$37$38$39$=$>$?$10$11$24+&6$2;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$2;#1000#7??????????8&$2;#8)##7???7000#100000001000$2;##8#&6$2;#3#7???8000#1!$2;#,8$29)$2;##8$2-40#40'$29#1000#7?????????>8&$29#8'$23#2#8'$24#1000#7??????????>'+$2@-1$24#32#38!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 816592 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<75=0+$2-40$3$4$5$6$7$2;+$23-1$29+$2-29$39$=$>$?$10$11+$24#1+&6$2;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$2;#1000#7??????????8&$2;#8)##7???7000#100000001000$2;##8#&6$2;#3#7???8000#1!$2;#,8$29)$2;##8$2-40#40'$29#1000#7?????????>8&$29#8'$23#2#8'$24#1000#7??????????>'+$2@-1$24#32#38!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 816592 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 816592 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbf64M.

Module LibSegNa_antbi16A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815648, 38%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 815648 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<7288+$2-30$3$4$5$6$7$;#2$29+$2-29@#100$:$=$>$?$10$11+$2-2<+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-29,1[,,1&8@#100$:&6@#1000000000000$:#38!$2-2<,2&8@#100$:&6@#1000000000000$:#38!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815648 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815648 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi16A.

Module LibSegNa_antbi16L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815648, 38%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [815788].
Definition STOPS1 : list Z := [815788] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;#1$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 815752 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<72:<#<72:<#5=#<72:<,20#$2<$2$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 815788 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815752 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815752 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi16L.

Module LibSegNa_antbi16M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815648, 38%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;$23$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#2'$24#1000#7??????????>'+$2@-1$24#2<#2<!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 815752 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<7288+$2-30$3$4$5$6$7$;#1$29+$2-29$39$=$>$?$10$11+$24#1+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#2'$24#1000#7??????????>'+$2@-1$24#2<#2<!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815752 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815752 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi16M.

Module LibSegNa_antbi32A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(811884, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 811884 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<63?0+$2-30$3$4$5$6$7$;#4$29+$2-29&8&9&6$:#8#??00%6$:#18@#100&9$:#??00%6$:#18$?$10$11+$2-30+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-29,1[,,1&8+@#1000000$:@#100&9$:#??00&8&9&6$:#8#??00%6$:#18!$2-30,4&8+@#1000000$:@#100&9$:#??00&8&9&6$:#8#??00%6$:#18!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 811884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 811884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi32A.

Module LibSegNa_antbi32L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(811884, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [812052].
Definition STOPS1 : list Z := [812052] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;#1$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 812016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6414#<6414#5=#<6414,20#$2<$2$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 812052 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 812016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 812016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi32L.

Module LibSegNa_antbi32M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(811884, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;$23$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#4'$24#1000#7??????????>'+$2@-1$24#2>#30!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 812016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<63?0+$2-30$3$4$5$6$7$;+$23-1$29+$2-29$39$=$>$?$10$11+$24#1+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#4'$24#1000#7??????????>'+$2@-1$24#2>#30!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 812016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 812016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi32M.

Module LibSegNa_antbi64A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815412, 59%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 815412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<71?0+$2-40$3$4$5$6$7$;#8$29+$2-29&8+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8&9&6$:#28#??00&6$:#38@#10000000000&9$:#??00+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8@#1000000&9$:#??0000@#100000000%6$:#18@#1000000&9$:#??0000$11+$2-38+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-29,1[,,1&8&8+@#100000000000000$:@#10000000000&9$:#??00&8@#1000000&9$:#??0000@#100000000%6$:#18&8+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8&9&6$:#28#??00&6$:#38!$2-38,8&8&8+@#100000000000000$:@#10000000000&9$:#??00&8@#1000000&9$:#??0000@#100000000%6$:#18&8+&9&6$:#18#??0000@#1000000%6&6$:#8#18&8&9&6$:#28#??00&6$:#38!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi64A.

Module LibSegNa_antbi64L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815412, 59%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [815636].
Definition STOPS1 : list Z := [815636] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$;#1$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 815600 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<7214#<7214#5=#<7214,20#$2<$2$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 815636 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815600 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi64L.

Module LibSegNa_antbi64M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815412, 59%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$;$23$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8'$23#2#8'$24#1000#7??????????>'+$2@-1$24#32#38!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 815600 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<71?0+$2-40$3$4$5$6$7$;+$23-1$29+$2-29$39$=$>$?$10$11+$24#1+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-40#40'$29#1000#7?????????>8&$29#8'$23#2#8'$24#1000#7??????????>'+$2@-1$24#32#38!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815600 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbi64M.

Module LibSegNa_antbu16A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(811736, 37%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 811736 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<633<+$2-30$3$4$5$6$7$;#2$29+$2-29&6$:#8$=$>$?$10$11+$2-2<+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-29,1[,,1&8@#100$:&6$:#8!$2-2<,2&8@#100$:&6$:#8!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 811736 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 811736 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu16A.

Module LibSegNa_antbu16L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(811736, 37%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [811872].
Definition STOPS1 : list Z := [811872] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;#1$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30"%pstring).
Definition ss0 : sym_state := SS 811836 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6360#<6360#5=#<6360,20#$2<$2$3$4$5$6$7$2=$2>$37$38$39$=$>$?$10$11$2?$30$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 811872 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 811836 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 811836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu16L.

Module LibSegNa_antbu16M.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(811736, 37%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$;$23$37$38$39$=$>$?$10$11$24+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#2'$24#1000#7??????????>'+$2@-1$24#2<#2<!$24#1,1$28'$28##??"%pstring).
Definition ss0 : sym_state := SS 811836 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<633<+$2-30$3$4$5$6$7$;#1$29+$2-29$39$=$>$?$10$11+$24#1+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-29,1$28%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8'$23#2#2'$24#1000#7??????????>'+$2@-1$24#2<#2<!$24#1,1$28'$28##??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 811836 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 811836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu16M.

Module LibSegNa_antbu32A.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(815800, 45%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [813596].
Definition STOPS1 : list Z := [813596] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8"%pstring).
Definition ss0 : sym_state := SS 815800 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<6:1<#<6:1<#5=#<6:1<,20##<733<+$2-30$3$4$5$6$7$;#4$29+$2-29&8&9&6$:#8#??00%6$:#18@#100&9$:#??00%6$:#18$?$10$11+$2-30+&6$;#3#7???8000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-29,1[,,1&8+@#1000000$:@#100&9$:#??00&8&9&6$:#8#??00%6$:#18!$2-30,4&8+@#1000000$:@#100&9$:#??00&8&9&6$:#8#??00%6$:#18!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801030#800000000000&$2#10($2-30#30'$;#1000#7??????????8&$;#8)##7???7000#100000001000$;##8#&6$;#3#7???8000#1!$;#,8$29)$;##8$2-30#30'$29#1000#7?????????>8&$29#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 813596 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 815800 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 815800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_antbu32A.

End BndP_Na_140.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001.
Module BndP_Na_100.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_100 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_44d4102ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA02BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA05XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthA03kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100?LibSegNa_qthA163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthCd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthDd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthEL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100>LibSegNa_qthGd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthH3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0152;BndP_Na_100=LibSegNa_qthI3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qthA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [412812].
Definition STOPS1 : list Z := [412812; 817696] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 39); (EVar 33); (EVar 42); (ELit 1); EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487520 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-352)) (ELit 352)].
Definition ss0 : sym_state := SS 817564 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-352), ELit 352)].
Definition F0L : list SR.region := [((EVar 2), (-352), 352)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64<8<#<7:20#64<8<#5=#64<8<,20##<7:1<+$2-160$3$4$5$6$7$2+$2-160#1:0#15?:78#1$2:#1$?$10$11$2:$21#7???8000$27#1$17$21$19$1:$1;$1<$1=$1>$1?,,14!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2-160,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801160#800000000000&$2#20($2-160#160,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 412812 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 817564 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 817564 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthA0.

Module LibSegNa_qthA16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [412812].
Definition STOPS1 : list Z := [412812; 817696] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2#10$3$4$5$6$7$8$9$21$27$21$2:#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487520 140737488355312;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-352)) (ELit 368)].
Definition ss0 : sym_state := SS 817564 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-336), ELit 352)].
Definition F0L : list SR.region := [((EVar 2), (-336), 352)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64<8<#<7:20#64<8<#5=#64<8<,20##<7:1<+$2-160$3$4$5$6$7+$2#10+$2-160#1:0#15?:78#1$2:#1$?$10$11$2:$21#7???8000$27#1$17$21$19$1:$1;$1<$1=$1>$1?,,14!$2-58,8$1;!$2-50,8$1:!$2-48,8$19!$2-40,8$18!$2-38,8$17!$2-30,8$16!$2-28,8$15!$2-20,8$14!$2-18,8$13!$2-10,8$12!$2-8,8$9!$2#,8$8!$2#8,8$1!$2-150,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801160#7??????????0&$2#20($2-160#170,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 412812 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 817564 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 817564 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthA16.

Module LibSegNa_qthB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [838104].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$32$;$<$=$>$?$10$11$2:$21#7???8000$27#1$17$21$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200"%pstring).
Definition ss0 : sym_state := SS 817692 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-280), ELit 8); ((EVar 2), (-256), ELit 8); ((EVar 2), (-192), ELit 8); ((EVar 2), (-200), ELit 8); ((EVar 2), (-240), ELit 8); ((EVar 50), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 52)].
Definition F0L : list SR.region := [((EVar 2), (-280), 8); ((EVar 2), (-256), 8); ((EVar 2), (-192), 8); ((EVar 2), (-200), 8); ((EVar 2), (-240), 8); ((EVar 50), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 52)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<<9=8#5=#<<9=8,20##<7;7<+$2-160$3$4$5$6$7$8+$2-160+$32#20$27+$2-88^#?#??????????????1$>$?$10$11+&6$32#3#7???8000$21#7???8000$27#1+$32#20$21$19$1:$32$1<$1=$1>$1?,,45!&6$32#3#7???8007,1#!$2-?0,8+&6$32#3#7???8000!&6$32#3#7???8006,1#!&6$32#3#7???8005,1#!&6$32#3#7???8004,1#!&6$32#3#7???8033,1^#?#??????????????3!&6$32#3#7???8032,1^#?#??????????????3!&6$32#3#7???8031,1^#?#??????????????3!&6$32#3#7???8030,1^#?#??????????????3!&6$32#3#7???802;,1^#?#??????????????2!&6$32#3#7???802:,1^#?#??????????????2!&6$32#3#7???8029,1^#?#??????????????2!&6$32#3#7???8028,1^#?#??????????????2!&6$32#3#7???8023,1^#?#??????????????2!&6$32#3#7???8022,1^#?#??????????????2!&6$32#3#7???8021,1^#?#??????????????2!&6$32#3#7???8020,1^#?#??????????????2!&6$32#3#7???801;,1^#?#??????????????2!&6$32#3#7???801:,1^#?#??????????????2!&6$32#3#7???8019,1^#?#??????????????2!&6$32#3#7???8018,1^#?#??????????????2!&6$32#3#7???8013,1^#?#??????????????2!&6$32#3#7???8012,1^#?#??????????????2!&6$32#3#7???8011,1^#?#??????????????2!&6$32#3#7???8010,1^#?#??????????????2!&6$32#3#7???800;,1^#?#??????????????2!&6$32#3#7???800:,1^#?#??????????????2!&6$32#3#7???8009,1^#?#??????????????2!&6$32#3#7???8008,1^#?#??????????????2!&6$32#3#7???802?,1^#?#??????????????8!&6$32#3#7???802>,1^#?#??????????????8!&6$32#3#7???802=,1^#?#??????????????8!&6$32#3#7???802<,1^#?#??????????????8!&6$32#3#7???8027,1^#?#??????????????8!&6$32#3#7???8026,1^#?#??????????????8!&6$32#3#7???8025,1^#?#??????????????8!&6$32#3#7???8024,1^#?#??????????????8!&6$32#3#7???801?,1^#?#??????????????8!&6$32#3#7???801>,1^#?#??????????????8!&6$32#3#7???801=,1^#?#??????????????8!&6$32#3#7???801<,1^#?#??????????????8!&6$32#3#7???8017,1^#?#??????????????8!&6$32#3#7???8016,1^#?#??????????????8!&6$32#3#7???8015,1^#?#??????????????8!&6$32#3#7???8014,1^#?#??????????????8!&6$32#3#7???800?,1^#?#??????????????8!&6$32#3#7???800>,1^#?#??????????????8!&6$32#3#7???800=,1^#?#??????????????8!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8003,1^#?#??????????????1!&6$32#3#7???8002,1^#?#??????????????1!&6$32#3#7???8001,1^#?#??????????????1!&6$32#3#7???8000,1^#?#??????????????1!$2-<8,8#7???8000!$32#10,8#<799<!$32#8,8#16502!$32#,8#41;58:;3!$2-<0,8$32!$2-100,8$2:!$2-118,8$32'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 838104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 817692 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 817692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthB.

Module LibSegNa_qthC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [838104].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168; 818064] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$21#7???8000$27#1+$32#20$21$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##!$32#20,1$2;'$2;##??'&9$2;#1##!$32#28,8#1!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000"%pstring).
Definition ss0 : sym_state := SS 818044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-264), ELit 8); ((EVar 2), (-304), ELit 8); ((EVar 2), (-248), ELit 8); ((EVar 2), (-208), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-264), 8); ((EVar 2), (-304), 8); ((EVar 2), (-248), 8); ((EVar 2), (-208), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,=#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<7;90#<<9=8#5=#<<9=8,20##<7;><+$2-160$3$4$5$6$7$8+$2-160+$32#60$21+$2-88$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$2;$26+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?,,23!$2-=0,8$21!&6$32#3#7???800?,1#!&6$32#3#7???800>,1#!&6$32#3#7???800=,1#!&6$32#3#7???800<,1#!$2-?8,8$21!$2-130,8#1!$2-108,8+$32#20'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##!$32#20,1$2;'$2;##??'&9$2;#1##!$32#28,8#1!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 838104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthC.

Module LibSegNa_qthCd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [838104].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168; 818064] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$21#7???8000$27#1+$32#20$21$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1!$32#20,1$2;'$2;##??'&9$2;#1##!$32#28,8#1!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000"%pstring).
Definition ss0 : sym_state := SS 818044 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-264), ELit 8); ((EVar 2), (-304), ELit 8); ((EVar 2), (-248), ELit 8); ((EVar 2), (-208), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-264), 8); ((EVar 2), (-304), 8); ((EVar 2), (-248), 8); ((EVar 2), (-208), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,=#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<7;90#<<9=8#5=#<<9=8,20##<7;><+$2-160$3$4$5$6$7$8+$2-160+$32#60$21+$2-88$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$2;$26+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?,,23!$2-=0,8$21!&6$32#3#7???800?,1#!&6$32#3#7???800>,1#!&6$32#3#7???800=,1#!&6$32#3#7???800<,1#!$2-?8,8$21!$2-130,8#1!$2-108,8+$32#20'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1!$32#20,1$2;'$2;##??'&9$2;#1##!$32#28,8#1!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 838104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818044 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818044 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthCd.

Module LibSegNa_qthD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [836056].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$2;$26+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#60,1$2<'$2<##??'&9$2<#1##'$2;##??'&9$2;#1##'&9$2;#2##'$26##??!$32#20,1$2;"%pstring).
Definition ss0 : sym_state := SS 818156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (96), ELit 1); ((EVar 50), (32), ELit 1); ((EVar 2), (-288), ELit 8)].
Definition F0L : list SR.region := [((EVar 50), (96), 1); ((EVar 50), (32), 1); ((EVar 2), (-288), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<<1=8#5=#<<1=8,20##<7<24+$2-160$3$4$5$6$7$8+$2-160+$32#60+$32#20&9$26#2$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$2;&6&5#&9$26#2#1+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?,,12!$32#20,1&9$2;#?=!$2-120,8&9$26#2!$32#60,1&9$2<#?='$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2<##??'&9$2<#1##'$2;##??'&9$2;#1##'&9$2;#2##'$26##??,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 836056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthD.

Module LibSegNa_qthDd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [836056].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$2;$26+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#60,1$2<'$2<##??'&9$2<#1#1#1'$2;##??'&9$2;#1##'&9$2;#2##'$26##??!$32#20,1$2;"%pstring).
Definition ss0 : sym_state := SS 818156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (96), ELit 1); ((EVar 50), (32), ELit 1); ((EVar 2), (-288), ELit 8)].
Definition F0L : list SR.region := [((EVar 50), (96), 1); ((EVar 50), (32), 1); ((EVar 2), (-288), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<<1=8#5=#<<1=8,20##<7<24+$2-160$3$4$5$6$7$8+$2-160+$32#60+$32#20&9$26#2$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$2;&6&5#&9$26#2#1+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?,,12!$32#20,1&9$2;#?=!$2-120,8&9$26#2!$32#60,1&9$2<#?='$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2<##??'&9$2<#1#1#1'$2;##??'&9$2;#1##'&9$2;#2##'$26##??,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 836056 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthDd.

Module LibSegNa_qthEG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827044].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$2=$;$<$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$15$2?+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##'$2=##1'$2?##1'$24^#8#:<7230489>80000^#?#???????????????!$32#60,1&9$2<#?='$2<##??'&9$2<#1##!$2-?8,8$21!$2-=0,8$21!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000!$32#68,8#1!$32#70,8$24!$32#30,8^#8#:<7230489>80000#&6$32#3#7???800<#4#&6$32#3#7???8004#4"%pstring).
Definition ss0 : sym_state := SS 818212 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-272), ELit 8); ((EVar 2), (-312), ELit 8); ((EVar 2), (-296), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (28), ELit 4); ((EVar 50), (224), ELit 1); ((EVar 50), (232), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-272), 8); ((EVar 2), (-312), 8); ((EVar 2), (-296), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (28), 4); ((EVar 50), (224), 1); ((EVar 50), (232), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",2!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4#5=#<9>:4,20##<7>08+$2-160$3$4$5$6$7$8+$2-160$21+$32#>0/5$24^#8#:<7230489>80000#7???8000$>$?$10$11+&6$32#3#7???8000+&6+$32#70#3#7???8000+&6+$32#30#3#7???8000+$32#60$21+$32#>0$21$19+$32#30+$32#70$1<$1=$1>$1?,,2?!$32#?8,8#!$32#?0,8/5$24^#8#:<7230489>80000!$32#>8,8#1!$32#>0,1#!&6$32#3#7???801?,1#!&6$32#3#7???801>,1#!&6$32#3#7???801=,1#!&6$32#3#7???801<,1#!$2-128,8$32!$2-138,8$2?!$2-110,8+$32#60'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##'$2=##1'$2?##1'$24^#8#:<7230489>80000^#?#???????????????!$32#60,1&9$2<#?='$2<##??'&9$2<#1##!$2-?8,8$21!$2-=0,8$21!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000!$32#68,8#1!$32#70,8$24!$32#30,8^#8#:<7230489>80000#&6$32#3#7???800<#4#&6$32#3#7???8004#4,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818212 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818212 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthEG.

Module LibSegNa_qthEL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160^#?#???????????????$;$<$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000$14$15$2?+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2?##1!$2-?0,8+&6$32#3#7???8000"%pstring).
Definition ss0 : sym_state := SS 818212 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-272), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), ELit 4); ((EVar 50), (160), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-272), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), 4); ((EVar 50), (160), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#7?058#5=#7?058,20##<7<80+$2-160$3$4$5$6$7$8+$2-160+$32#:8##18$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000$2?+$32#60$2?+$32#:0+$32#60$19+$32#30$32$1<$1=$1>$1?,,11!$32#:0,1#!&6$32#3#7???8017,1#!&6$32#3#7???8016,1#!&6$32#3#7???8015,1#!&6$32#3#7???8014,1#!$2-110,8+$32#60'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2?##1!$2-?0,8+&6$32#3#7???8000,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818212 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818212 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthEL.

Module LibSegNa_qthF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827044].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$13$2?+$32#60$16+$32#:0+$32#60$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487520 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-352)) (ELit 352);
   KWord (SA (EVar 2) (-248)) 8 (EVar 33)].
Definition ss0 : sym_state := SS 818304 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4#5=#<9>:4,20##<7<90+$2-160$3$4$5$6$7$8+$2-160$21+$32#:0$<$=$>$?$10$11+&6$32#3#7???8000$21$2?+$32#60$16+$32#:0+$32#60$19$1:$32$1<$1=$1>$1?,,4'$2#7???7?801160#800000000000&$2#20($2-160#160!$2-?8,8$21,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818304 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818304 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthF.

Module LibSegNa_qthG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827044].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$21$2?+$32#60$16+$32#:0$18$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##'$2?##1!$32#:0,1#!$2-<8,8#7???8000!$2-118,8$32!$2-100,8$2:!$2-108,8+$32#20"%pstring).
Definition ss0 : sym_state := SS 818320 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), ELit 4); ((EVar 33), (0), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), 4); ((EVar 33), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4#5=#<9>:4,20##<7=04+$2-160$3$4$5$6$7$8+$2-160$2:+$32#60$<$=$>$?$10$11+&6$32#3#7???8000$2:+$32#20+$32#60#7???8000+$32#:0$32$19$1:$32$1<$1=$1>$1?,,1?!$21#,1&8&9$26#?=@#2$2?!&6$32#3#7???8017,1^#?#??????????????8!&6$32#3#7???8016,1^#?#??????????????8!&6$32#3#7???8015,1^#?#??????????????8!&6$32#3#7???8014,1^#?#??????????????8'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$26##??'&9$26#1##'$2?##1!$32#:0,1#!$2-<8,8#7???8000!$2-118,8$32!$2-100,8$2:!$2-108,8+$32#20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthG.

Module LibSegNa_qthGd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827044].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$21$2?+$32#60$16+$32#:0$18$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1'$2?##1!$32#:0,1#!$2-<8,8#7???8000!$2-118,8$32!$2-100,8$2:!$2-108,8+$32#20"%pstring).
Definition ss0 : sym_state := SS 818320 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), ELit 4); ((EVar 33), (0), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (20), 4); ((EVar 33), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4#5=#<9>:4,20##<7=04+$2-160$3$4$5$6$7$8+$2-160$2:+$32#60$<$=$>$?$10$11+&6$32#3#7???8000$2:+$32#20+$32#60#7???8000+$32#:0$32$19$1:$32$1<$1=$1>$1?,,1?!$21#,1&8&9$26#?=@#2$2?!&6$32#3#7???8017,1^#?#??????????????8!&6$32#3#7???8016,1^#?#??????????????8!&6$32#3#7???8015,1^#?#??????????????8!&6$32#3#7???8014,1^#?#??????????????8'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$26##??'&9$26#1#1#1'$2?##1!$32#:0,1#!$2-<8,8#7???8000!$2-118,8$32!$2-100,8$2:!$2-108,8+$32#20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthGd.

Module LibSegNa_qthH.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [820460].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$2:+$32#20+$32#60#7???8000$17$32$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40!$2:#,1$30'$30##??'$26##??!$2-120,8&9$26#2"%pstring).
Definition ss0 : sym_state := SS 818436 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 42), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 42), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,=#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<84><#<84><#5=#<84><,20#$1+$2-160$3$4$5$6$7$8+$2-160&8&9$30#?=&9$26#2&9$26#2$<$=$>$?$10$11+&6$32#3#7???8000$2:+$32#20+$32#60#7???8000$17$32$19$1:$32$1<$1=$1>$1?,,16!$2:#,1&8&9$30#?=&9$26#2'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40'$30##??'$26##??!$2-120,8&9$26#2,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 820460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818436 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818436 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthH.

Module LibSegNa_qthI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827044].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12+&6+$32#70#3#7???8000+&6+$32#30#3#7???8000+$32#60$21+$32#>0$18$19+$32#30+$32#70$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$24^#8#:<7230489>80000^#?#???????????????!$32#>0,1#!$2-?0,8+&6$32#3#7???8000!$32#70,8$24!$32#30,8^#8#:<7230489>80000!$2-128,8$32!$2-100,8$2:#&6$32#3#7???800<#4#&6$32#3#7???8004#4"%pstring).
Definition ss0 : sym_state := SS 818696 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (28), ELit 4); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (36), ELit 4); ((EVar 50), (288), ELit 1); ((EVar 50), (296), ELit 24)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (28), 4); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (36), 4); ((EVar 50), (288), 1); ((EVar 50), (296), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",2!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<9>:4#5=#<9>:4,20##<7>94+$2-160$3$4$5$6$7$8+$2-160$2:+$32#120$<$=$>$?$10$11$12+&6+$32#70#3#7???8000+&6+$32#30#3#7???8000+$32#60$21+$32#120$18$19+$32#30$32$1<$1=$1>$1?,,1>!$32#138,8#!$32#130,8/7$24^#8#:<7230489>80000!$32#128,8&4#/7$24^#8#:<7230489>80000!$32#120,1#!&6$32#3#7???8027,1#!&6$32#3#7???8026,1#!&6$32#3#7???8025,1#!&6$32#3#7???8024,1#!&6$32#3#7???801?,1^#?#??????????????8!&6$32#3#7???801>,1^#?#??????????????8!&6$32#3#7???801=,1^#?#??????????????8!&6$32#3#7???801<,1^#?#??????????????8'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$24^#8#:<7230489>80000^#?#???????????????!$32#>0,1#!$2-?0,8+&6$32#3#7???8000!$32#70,8$24!$32#30,8^#8#:<7230489>80000!$2-128,8$32!$2-100,8$2:#&6$32#3#7???800<#4#&6$32#3#7???8004#4,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 827044 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818696 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818696 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthI.

End BndP_Na_100.
