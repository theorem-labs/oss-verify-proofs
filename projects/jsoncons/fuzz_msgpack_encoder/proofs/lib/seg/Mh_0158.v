(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_001. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Ns_030.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_030 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_4fb4cc2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb52BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb55XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb53kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb92BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb92BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb95XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb94planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_fiPb93kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_fiPx3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_3655642ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbEs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030?LibSegNs_ad_gbR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030@LibSegNs_ad_gbTs3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_69e99a2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A012BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A013NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A012BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A015XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A012F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A013PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A014planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A015regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_030ALibSegNs_ad_i6A013kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ad_fiPb5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4fb4cc.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4fb4cc.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-140$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11+$2-121+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483392 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KWord (SA (EVar 2) (-290)) 1 (EVar 46);
   KRange (EVar 46) 0 255].
Definition ss0 : sym_state := SS 250412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3=22<+$2-140$3$4$5$6$7$24$9$24$2>$<$=$>$?$10$11+$2-122+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-122,1$2>'$2>##??,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4fb4cc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 250412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4fb4cc.IT BndT_Ns_000.SegItab_Ns_4fb4cc.IT_sound BF NX0 BR XSTEP F0 PSS plan 250412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_fiPb5.

Module LibSegNs_ad_fiPb6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4fb4cc.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4fb4cc.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-140$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11+$2-120+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483392 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KWord (SA (EVar 2) (-289)) 1 (EVar 46);
   KRange (EVar 46) 0 255].
Definition ss0 : sym_state := SS 250412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3=22<+$2-140$3$4$5$6$7$24$9$24$2>$<$=$>$?$10$11+$2-121+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-121,1$2>'$2>##??,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4fb4cc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 250412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4fb4cc.IT BndT_Ns_000.SegItab_Ns_4fb4cc.IT_sound BF NX0 BR XSTEP F0 PSS plan 250412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_fiPb6.

Module LibSegNs_ad_fiPb7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4fb4cc.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4fb4cc.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-140$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11+$2-11?+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483392 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KWord (SA (EVar 2) (-288)) 1 (EVar 46);
   KRange (EVar 46) 0 255].
Definition ss0 : sym_state := SS 250412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3=22<+$2-140$3$4$5$6$7$24$9$24$2>$<$=$>$?$10$11+$2-120+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-120,1$2>'$2>##??,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4fb4cc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 250412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4fb4cc.IT BndT_Ns_000.SegItab_Ns_4fb4cc.IT_sound BF NX0 BR XSTEP F0 PSS plan 250412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_fiPb7.

Module LibSegNs_ad_fiPb8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4fb4cc.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4fb4cc.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-140$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11+$2-11>+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483392 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KWord (SA (EVar 2) (-287)) 1 (EVar 46);
   KRange (EVar 46) 0 255].
Definition ss0 : sym_state := SS 250412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3=22<+$2-140$3$4$5$6$7$24$9$24$2>$<$=$>$?$10$11+$2-11?+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-11?,1$2>'$2>##??,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4fb4cc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 250412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4fb4cc.IT BndT_Ns_000.SegItab_Ns_4fb4cc.IT_sound BF NX0 BR XSTEP F0 PSS plan 250412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_fiPb8.

Module LibSegNs_ad_fiPb9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4fb4cc.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4fb4cc.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-140$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11+$2-11=+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483392 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KWord (SA (EVar 2) (-286)) 1 (EVar 46);
   KRange (EVar 46) 0 255].
Definition ss0 : sym_state := SS 250412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3=22<+$2-140$3$4$5$6$7$24$9$24$2>$<$=$>$?$10$11+$2-11>+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-11>,1$2>'$2>##??,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4fb4cc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 250412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4fb4cc.IT BndT_Ns_000.SegItab_Ns_4fb4cc.IT_sound BF NX0 BR XSTEP F0 PSS plan 250412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_fiPb9.

Module LibSegNs_ad_fiPx.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4fb4cc.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4fb4cc.IT.
Definition ENDS : list Z := [250448].
Definition STOPS1 : list Z := [250448] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-140$3$4$5$6$7$24$2=$:$;$<$=$>$?$10$11+$2-127+$2-127$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 250412 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3=250#3=250#5=#3=250,20#$28$2$3$4$5$6$7$29$2:$2=$;$<$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?800140#800000000000&$2#10($2-140#140!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 250448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4fb4cc.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 250412 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4fb4cc.IT BndT_Ns_000.SegItab_Ns_4fb4cc.IT_sound BF NX0 BR XSTEP F0 PSS plan 250412 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_fiPx.

Module LibSegNs_ad_gbEl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [418700].
Definition STOPS1 : list Z := [418700] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$26+$22@-1$26$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#10,8$25'$26#19#80000000'$22#1:#40000000'+$22@-1$26#1#40000000"%pstring).
Definition ss0 : sym_state := SS 418552 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6638<#6638<#5;#66384,20#$1+$2-50$3$4$5$6$7$:$26@#2$26+@-1$26-9$22$=$>$?$10$11$10$?$>$25$=$17$18$19$1:$1;$1<$1=$1>$1?,,18!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#10,8$25'$26#19#80000000'$22#1:#40000000'+$22@-1$26#1#40000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6638<#6638<#5:#6638<,20#$1+$2-50$3$4$5$6$7$:$26@#2$26+@-1$26-9$22$=$>$?$10$11$10$?$>$25$=$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4@#2$26$22#1#1!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#10,8$25'$26#19#80000000'$22#1:#40000000'+$22@-1$26#1#40000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6638<#6638<#5=#6638<,20#$1+$2-50$3$4$5$6$7$:$26@#2$26+@-1$26-9@#2$26$=$>$?$10$11$10$?$>$25$=$17$18$19$1:$1;$1<$1=$1>$1?,,19'&4@#2$26$22##!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#10,8$25'$26#19#80000000'$22#1:#40000000'+$22@-1$26#1#40000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 418700 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418552 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418552 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbEl.

Module LibSegNs_ad_gbEs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [418700].
Definition STOPS1 : list Z := [418700] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:#16+$22-16$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1@#2$23'$23##16'&9@#2$23#1##'$22#17#40000000"%pstring).
Definition ss0 : sym_state := SS 418552 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6638<#6638<#5;#66384,20#$1+$2-50$3$4$5$6$7$:#16#2<^#?#?????????????>1$22$=$>$?$10$11$10$?$>+$:#1$=$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1@#2$23'$23##16'&9@#2$23#1##'$22#17#40000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6638<#6638<#5:#6638<,20#$1+$2-50$3$4$5$6$7$:#16#2<^#?#?????????????>1$22$=$>$?$10$11$10$?$>+$:#1$=$17$18$19$1:$1;$1<$1=$1>$1?,,16'&4#2<$22#1#1!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1@#2$23'$23##16'&9@#2$23#1##'$22#17#40000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6638<#6638<#5=#6638<,20#$1+$2-50$3$4$5$6$7$:#16#2<^#?#?????????????>1#2<$=$>$?$10$11$10$?$>+$:#1$=$17$18$19$1:$1;$1<$1=$1>$1?,,16'&4#2<$22##!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50'$:#7???7?800050#7?????????>8&$:#8)$2-50#50$:##18($:##18!$:#,1@#2$23'$23##16'&9@#2$23#1##'$22#17#40000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418700 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 418700 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418552 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418552 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbEs.

Module LibSegNs_ad_gbF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [418876].
Definition STOPS1 : list Z := [418876] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800050#800000000000&$2#10($2-50#50'$8#7???7?800050#7?????????>8&$8#8)$2-50#50$8##18($8##18'$17#30#80000000!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31"%pstring).
Definition ss0 : sym_state := SS 418820 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 8), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 8), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6643<#6643<#5=#6643<,20#$28$2$3$4$5$6$7$29$2:+@#2&6$17#1#1$;$<$=$>$?$10$11$2;$2<$2=$2>$2?$30$31$19$1:$1;$1<$1=$1>$1?,,14!$8#10,8$18!$8#,8+@#2&6$17#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50'$8#7???7?800050#7?????????>8&$8#8)$2-50#50$8##18($8##18'$17#30#80000000!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418820 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418820 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbF.

Module LibSegNs_ad_gbN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [761212; 418768].
Definition STOPS1 : list Z := [761212; 418768] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483152 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 35) 0 1073741824].
Definition ss0 : sym_state := SS 418744 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;9=7<#663=0#;9=7<#663=0#5;#663;<,20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$23$15$16$17$:$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800050#800000000000&$2#10($2-50#50'$23##40000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;9=7<#663=0#;9=7<#663=0#5:#663=0,20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$23$15$16$17$:$19$1:$1;$1<$1=$1>$1?,,5'&4&1$23##1#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50'$23##40000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#;9=7<#663=0#;9=7<#663=0#5=#;9=7<,20##663=0+$2-50$3$4$5$6$7$8$9$:$15$23$=$>$?$10$11$12$13$23$15$16$17$:$19$1:$1;$1<$1=$1>$1?,,5'&4&1$23##1##'$2#7???7?800050#800000000000&$2#10($2-50#50'$23##40000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 761212 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 418768 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418744 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbN.

Module LibSegNs_ad_gbR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$24$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483152 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 36) 44 2147483648].
Definition ss0 : sym_state := SS 418700 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##663;8+$2-50$3$4$5$6$7$8$9+@#8&6$24#3#8$;$24$=$>$?$10$11$12$13$14$15$16+@#8&6$24#3#8$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800050#800000000000&$2#10($2-50#50'$24#2<#80000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418700 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418700 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbR.

Module LibSegNs_ad_gbTd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12#$23$15$23$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483152 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-80)) (ELit 80);
   KRange (EVar 9) 25 2147483648;
   KRange (EVar 35) 0 2147483648].
Definition ss0 : sym_state := SS 418768 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##66404+$2-50$3$4$5$6$7$8$9$15+$9#1$<$=$>$?$10$11$12#$23$15$23$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?800050#800000000000&$2#10($2-50#50'$9#19#80000000'$23##80000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418768 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418768 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbTd.

Module LibSegNs_ad_gbTs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_365564.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_365564.IT.
Definition ENDS : list Z := [418876].
Definition STOPS1 : list Z := [418876] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8#16$:$;$<$=$>$?$10$11$12#$23$15$23$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800050#800000000000&$2#10($2-50#50'$8#7???7?800050#7?????????>8&$8#8)$2-50#50$8##18($8##18'$23##16'$17#30#80000000!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31"%pstring).
Definition ss0 : sym_state := SS 418768 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 8), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 8), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6643<#6643<#5=#6643<,20#$28$2$3$4$5$6$7$29$2:+@#2&6$17#1#1#17$<$=$>$?$10$11$2;$2<$2=$2>$2?$30$31$19$1:$1;$1<$1=$1>$1?,,15!$8#10,8$18!$8#,8+@#2&6$17#1#1'$2#7???7?800050#800000000000&$2#10($2-50#50'$8#7???7?800050#7?????????>8&$8#8)$2-50#50$8##18($8##18'$23##16'$17#30#80000000!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418876 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_365564.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418768 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_365564.IT BndT_Ns_000.SegItab_Ns_365564.IT_sound BF NX0 BR XSTEP F0 PSS plan 418768 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_gbTs.

Module LibSegNs_ad_i6A01.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [238524].
Definition STOPS1 : list Z := [238524] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#!$25-10,4#1,$25-8#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$35"%pstring).
Definition ss0 : sym_state := SS 238448 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:3;<#3:3;<#5=#3:3;<,20#$28$2$3$4$5$6$7$29$2:#1#1##2$>$?$10$11$2;$2<$35$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$25-8,8+$40#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#!$25-10,4#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$35,41!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 238524 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238448 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238448 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6A01.

End BndP_Ns_030.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_000.
Module BndP_Ns_032.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_032 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_69e99a2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILL3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KILS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KISS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6Kbz3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_6ceef52ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdL23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032BLibSegNs_ad_i6KdS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6R23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032ALibSegNs_ad_i6V1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032@LibSegNs_ad_i6V23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_2729c02ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_032?LibSegNs_ad_isG3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ad_i6KILL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [249068].
Definition STOPS1 : list Z := [249068] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1$32'$32##??'&9$32#1#1#1!$24#38,8$33!$24#40,8$34'$33##80000000'$34#1000#7??????00000!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000"%pstring).
Definition ss0 : sym_state := SS 238184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<<><#3<<><#5=#3<<><,20##3:364+$2-40$3$4$5$6$7$24+$24#30+$24#30+$33$34$30+$2?$30$2?$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1$32'$32##??'&9$32#1#1#1!$24#38,8$33!$24#40,8$34'$33##80000000'$34#1000#7??????00000!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249068 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6KILL.

Module LibSegNs_ad_i6KILS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [249068].
Definition STOPS1 : list Z := [249068] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1$32'$32##??'&9$32#1#1#1!$24#38,8$33!$24#40,8$34'$33##80000000'$34#1000#7??????00000!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##"%pstring).
Definition ss0 : sym_state := SS 238184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<<><#3<<><#5=#3<<><,20##3:364+$2-40$3$4$5$6$7$24+$24#30+$24#30+$33$34+$24#19++$24$2=#19$2=$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1$32'$32##??'&9$32#1#1#1!$24#38,8$33!$24#40,8$34'$33##80000000'$34#1000#7??????00000!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249068 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6KILS.

Module LibSegNs_ad_i6KISL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [249068].
Definition STOPS1 : list Z := [249068] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1@#2$31'$31##16'&9@#2$31#1##!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000"%pstring).
Definition ss0 : sym_state := SS 238184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<<><#3<<><#5=#3<<><,20##3:364+$2-40$3$4$5$6$7$24+$24#30+$24#30++$24$31#31$30+$2?$30$2?$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1@#2$31'$31##16'&9@#2$31#1##!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249068 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6KISL.

Module LibSegNs_ad_i6KISS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [249068].
Definition STOPS1 : list Z := [249068] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1@#2$31'$31##16'&9@#2$31#1##!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##"%pstring).
Definition ss0 : sym_state := SS 238184 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<<><#3<<><#5=#3<<><,20##3:364+$2-40$3$4$5$6$7$24+$24#30+$24#30++$24$31#31+$24#19++$24$2=#19$2=$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48!$24#30,1@#2$31'$31##16'&9@#2$31#1##!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249068 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6KISS.

Module LibSegNs_ad_i6Kbn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-10,4#!$25-8,8$27'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3:268+$2-40$3$4$5$6$7$24$9+$24#30#2<#1$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-10,4#!$25-8,8$27'$27#1^#?#???????????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6Kbn.

Module LibSegNs_ad_i6Kbz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [238184].
Definition STOPS1 : list Z := [238184] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-10,4#!$25-8,8#"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:268#3:268#5=#3:268,20#$1+$2-40$3$4$5$6$7$24$9##1#1$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-10,4#!$25-8,8#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 238184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6Kbz.

Module LibSegNs_ad_i6KdL2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_6ceef5.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_6ceef5.IT.
Definition ENDS : list Z := [264208].
Definition STOPS1 : list Z := [264208] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",23'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18$26##38)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#!$25-10,4#'$26#7???7?800040#7?????????<8)$2-40#40$26##38)$24##60$26##38!$26#,8#;?>30!$24#10,8$26%#10000#<6<<0!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000)$30##1$26##38"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-64), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40810#40810#5=#40810,20##3:350+$2-40$3$4$5$6$7$24$9$26+$2-40$12$9#40810$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,25!$2-38,8$2?!$2-40,8$30'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18$26##38)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#!$25-10,4#'$26#7???7?800040#7?????????<8)$2-40#40$26##38)$24##60$26##38!$26#,8#;?>30!$24#10,8$26%#10000#<6<<0!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000)$30##1$26##38,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_6ceef5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_6ceef5.IT BndT_Ns_001.SegItab_Ns_6ceef5.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6KdL2.

Module LibSegNs_ad_i6KdS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_6ceef5.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_6ceef5.IT.
Definition ENDS : list Z := [264208].
Definition STOPS1 : list Z := [264208] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18$26##38)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#!$25-10,4#'$26#7???7?800040#7?????????<8)$2-40#40$26##38)$24##60$26##38!$26#,8#;?>30!$24#10,8$26%#10000#<6<<0!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-64), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40810#40810#5=#40810,20##3:350+$2-40$3$4$5$6$7$24$9$26+$2-40$12$9#40810$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$2-38,8$2=!$2-40,8+$24#19'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18$26##38)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#!$25-10,4#'$26#7???7?800040#7?????????<8)$2-40#40$26##38)$24##60$26##38!$26#,8#;?>30!$24#10,8$26%#10000#<6<<0!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264208 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_6ceef5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_6ceef5.IT BndT_Ns_001.SegItab_Ns_6ceef5.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6KdS2.

Module LibSegNs_ad_i6R1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_6ceef5.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_6ceef5.IT.
Definition ENDS : list Z := [238448].
Definition STOPS1 : list Z := [238448] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 238152 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:370#3:370#5=#3:370,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 238448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_6ceef5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238152 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_6ceef5.IT BndT_Ns_001.SegItab_Ns_6ceef5.IT_sound BF NX0 BR XSTEP F0 PSS plan 238152 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6R1.

Module LibSegNs_ad_i6R2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_6ceef5.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_6ceef5.IT.
Definition ENDS : list Z := [238448].
Definition STOPS1 : list Z := [238448] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 238416 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:370#3:370#5=#3:370,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 238448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_6ceef5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238416 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_6ceef5.IT BndT_Ns_001.SegItab_Ns_6ceef5.IT_sound BF NX0 BR XSTEP F0 PSS plan 238416 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6R2.

Module LibSegNs_ad_i6V1n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8$27'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3:20<+$2-40$3$4$5$6$7$24+$24#30+$24#30#2<#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8$27'$27#1^#?#???????????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6V1n.

Module LibSegNs_ad_i6V1z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [238092].
Definition STOPS1 : list Z := [238092] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8#"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:20<#3:20<#5=#3:20<,20#$1+$2-40$3$4$5$6$7$24+$24#30##1#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 238092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6V1z.

Module LibSegNs_ad_i6V2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_69e99a.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_69e99a.IT.
Definition ENDS : list Z := [238092].
Definition STOPS1 : list Z := [238092] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#2!$25-10,4#1"%pstring).
Definition ss0 : sym_state := SS 238032 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:20<#3:20<#5=#3:20<,20#$1+$2-40$3$4$5$6$7$24+$24#30$25#2#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#2!$25-10,4#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 238092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_69e99a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 238032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_69e99a.IT BndT_Ns_001.SegItab_Ns_69e99a.IT_sound BF NX0 BR XSTEP F0 PSS plan 238032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_i6V2.

Module LibSegNs_ad_isG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [249576].
Definition STOPS1 : list Z := [249576] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#10,8$29'$22##20000000'$24#1#20000000"%pstring).
Definition ss0 : sym_state := SS 249520 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 9), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<>>8#3<>>8#5=#3<>>8,20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24$29$16$17$18$19$1:$1;$1<$1=$1>$1?,,;!$9#8,8+$22$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#10,8$29'$22##20000000'$24#1#20000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249520 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249520 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isG.

End BndP_Ns_032.
Module BndP_Ns_033.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_033 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_2729c02ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isL3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isRs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_isS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_isTs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033ALibSegNs_ad_isTs23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_3ac1be2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_iwS3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_652f5f2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033@LibSegNs_ad_jsRs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_033?LibSegNs_ad_jsS3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ad_isL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [249576; 418552].
Definition STOPS1 : list Z := [249576; 418552] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$24$22$25+$25$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249388 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3<>>8#662?8#3<>>8#662?8#5;#3<>98,20#$1+$2-40$3$4$5$6$7$22$:$26+@#2&6$26#1-1++@-1$22@#2&6$26#1-1$22+$25$24$?$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3<>>8#662?8#3<>>8#662?8#5=#662?8,20##3<>;0+$2-40$3$4$5$6$7$22$:$:+@#2&6$26#1-1++$22+$24@-2&6$26#1#1$22$22#$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4++@-1$22@#2&6$26#1-1$24#1#1!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3<>>8#662?8#3<>>8#662?8#5=#3<>>8,20#$1+$2-40$3$4$5$6$7$22$:#1+@#2&6$26#1-1++@-1$22@#2&6$26#1-1$22+$25$24$?$24$11$25+$24$25+$22$24$27$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4++@-1$22@#2&6$26#1-1$24##!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 418552 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isL.

Module LibSegNs_ad_isRl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [249692].
Definition STOPS1 : list Z := [249692] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1!$9#10,8$29'$29#1000#7??????00000'$22##20000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32"%pstring).
Definition ss0 : sym_state := SS 249632 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<?5<#3<?5<#5=#3<?5<,20#$2<$2$3$4$5$6$7$2=$2>+$22$29$;$<$=$>$?$10$11$2?$30$31$32$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1!$9#10,8$29'$29#1000#7??????00000'$22##20000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isRl.

Module LibSegNs_ad_isRs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [249692].
Definition STOPS1 : list Z := [249692] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$2:'$2:##16'&9@#2$2:#1##'$22##16!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32"%pstring).
Definition ss0 : sym_state := SS 249632 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3<?5<#3<?5<#5=#3<?5<,20#$2<$2$3$4$5$6$7$2=$2>++$9$22#1$;$<$=$>$?$10$11$2?$30$31$32$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$2:'$2:##16'&9@#2$2:#1##'$22##16!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249692 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isRs.

Module LibSegNs_ad_isS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [249576; 418552].
Definition STOPS1 : list Z := [249576; 418552] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$24$22$25+$25$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249388 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3<>>8#662?8#3<>>8#662?8#5;#3<>98,20#$1+$2-40$3$4$5$6$7$22$:$26#16+@-1$22#16$22+$25$24$?$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3<>>8#662?8#3<>>8#662?8#5=#662?8,20##3<>;0+$2-40$3$4$5$6$7$22$:$:#16++$22$24-16$22$22#$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4+@-1$22#16$24#1#1!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3<>>8#662?8#3<>>8#662?8#5=#3<>>8,20#$1+$2-40$3$4$5$6$7$22$:##16+@-1$22#16$22+$25$24$?$24$11$25+$24$25+$22$24+$:#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4+@-1$22#16$24##!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 249576 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 418552 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isS.

Module LibSegNs_ad_isTl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24$29$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1'$22##20000000'$24#1#20000000'$29#1000#7??????00000(+$29+$22$24##1)+$29+$22$24##1$9##18)$2-40#40+$29+$22$24##1'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (8), ELit 8); ((EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 9), (8), 8); ((EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##3<?20+$2-40$3$4$5$6$7$22$9+$22$29$25$24$=$>$?$10$11$25+$25$24+$22+$24$29$29$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!+$22+$24$29#,1#!$9#8,8+$22$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1'$22##20000000'$24#1#20000000'$29#1000#7??????00000(+$29+$22$24##1)+$29+$22$24##1$9##18)$2-40#40+$29+$22$24##1'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249576 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isTl.

Module LibSegNs_ad_isTs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$22'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 9), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##3<?20+$2-40$3$4$5$6$7$22$9++$9$22#1$25$24$=$>$?$10$11$25+$25$24++$9+$22$24#1+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!+$9+$22$24#1,1#!$9#,1+@#2$22@#2$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249576 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isTs.

Module LibSegNs_ad_isTs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2729c0.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2729c0.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$22'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249576 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (0), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 9) (ELit 1)) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 9), (0), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 9) (ELit 1)) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##3<?20+$2-40$3$4$5$6$7$22$9++$9$22#1$25$24$=$>$?$10$11$25+$25$24++$9+$22$24#1+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!+$9+$22$24#1,1#!$9#,1+@#2$22@#2$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2729c0.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249576 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2729c0.IT BndT_Ns_000.SegItab_Ns_2729c0.IT_sound BF NX0 BR XSTEP F0 PSS plan 249576 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_isTs2.

Module LibSegNs_ad_iwL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3ac1be.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3ac1be.IT.
Definition ENDS : list Z := [249344; 249388; 249176].
Definition STOPS1 : list Z := [249344; 249388; 249176] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$23+$27$22$25+$25$24$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249068 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5;#3<=24,20#$1+$2-40$3$4$5$6$7$24$23$27+$27$22$21$25+$24$25#1$10$11+$22$27$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5=#3<>00,20#$1$2$3$4$5$6$7$8$9+$22$27+$27$22$21$25+$24$25#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16'&4&1$24##1#1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5;#3<=48,20#$1+$2-40$3$4$5$6$7$24$23$27+$27$22$22$25+$24$25#1$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5=#3<>2<,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4$25$27#1#1'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5;#3<=54,20#$1+$2-40$3$4$5$6$7$24$23++$22$27#1+$27$22$22$25+$24$25#1$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4$25$27##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5:#3<=58,20#$1+$2-40$3$4$5$6$7$24$23++$22$27#1+$27$22$22$25+$24$25#1$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'&4$25++$22$27#1#1#1'&4$25$27##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5=#3<>2<,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'&4$25++$22$27#1##'&4$25$27##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 3)) (SGA.mkplan (fst ex10) (SGP.PEnd 2))))))).
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
Definition ps0 : SR.post_spec := SR.PS 249344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 249388 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 249388 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s9).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s9).
Definition ps3 : SR.post_spec := SR.PS 249176 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3ac1be.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249068 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3ac1be.IT BndT_Ns_000.SegItab_Ns_3ac1be.IT_sound BF NX0 BR XSTEP F0 PSS plan 249068 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_iwL.

Module LibSegNs_ad_iwS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3ac1be.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3ac1be.IT.
Definition ENDS : list Z := [249344; 249388; 249176].
Definition STOPS1 : list Z := [249344; 249388; 249176] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$23+$23+$22#1$25+$25$24$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 249068 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5;#3<=30,20#$1+$2-40$3$4$5$6$7$24$23+$23#1+$23+$22#1@#2$22$25+$24$25#$10$11++$22$23#1$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5=#3<>00,20#$1$2$3$4$5$6$7$8$9++$22$23#1+$23+$22#1@#2$22$25+$24$25#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'&4&1$24##1#1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5;#3<=48,20#$1+$2-40$3$4$5$6$7$24$23+$23#1+$23+$22#1$22$25+$24$25#$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5=#3<>2<,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'&4$25+$23#1#1#1'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5;#3<=54,20#$1+$2-40$3$4$5$6$7$24$23++$22$23#2+$23+$22#1$22$25+$24$25#$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'&4$25+$23#1##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5:#3<=58,20#$1+$2-40$3$4$5$6$7$24$23++$22$23#2+$23+$22#1$22$25+$24$25#$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4$25++$22$23#2#1#1'&4$25+$23#1##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3<>00#3<>2<#3<=58#3<>00#3<>2<#3<=58#5=#3<>2<,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4$25++$22$23#2##'&4$25+$23#1##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 3)) (SGA.mkplan (fst ex10) (SGP.PEnd 2))))))).
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
Definition ps0 : SR.post_spec := SR.PS 249344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 249388 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 249388 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s9).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s9).
Definition ps3 : SR.post_spec := SR.PS 249176 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3ac1be.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 249068 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3ac1be.IT BndT_Ns_000.SegItab_Ns_3ac1be.IT_sound BF NX0 BR XSTEP F0 PSS plan 249068 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_iwS.

Module LibSegNs_ad_jsG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [256772].
Definition STOPS1 : list Z := [256772] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#10,8$29'$22##20000000'$24#1#20000000"%pstring).
Definition ss0 : sym_state := SS 256716 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 9), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>;04#3>;04#5=#3>;04,20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24$29$16$17$18$19$1:$1;$1<$1=$1>$1?,,;!$9#8,8+$22$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#10,8$29'$22##20000000'$24#1#20000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256716 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256716 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsG.

Module LibSegNs_ad_jsL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [256772; 418552].
Definition STOPS1 : list Z := [256772; 418552] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$24$22$25+$25$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256584 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3>;04#662?8#3>;04#662?8#5;#3>:;4,20#$1+$2-40$3$4$5$6$7$22$:$26+@#2&6$26#1-1++@-1$22@#2&6$26#1-1$22+$25$24$?$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3>;04#662?8#3>;04#662?8#5=#662?8,20##3>:<<+$2-40$3$4$5$6$7$22$:$:+@#2&6$26#1-1++$22+$24@-2&6$26#1#1$22$22#$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4++@-1$22@#2&6$26#1-1$24#1#1!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3>;04#662?8#3>;04#662?8#5=#3>;04,20#$1+$2-40$3$4$5$6$7$22$:#1+@#2&6$26#1-1++@-1$22@#2&6$26#1-1$22+$25$24$?$24$11$25+$24$25+$22$24$27$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<'&4++@-1$22@#2&6$26#1-1$24##!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1$21'$21##??'&9$21#1#1#1!$:#8,8$22'$22##20000000!$:#10,8$27'$27#1000#7??????00000!$:#,8$26'$26#1;#40000001'&9$26#1#1#1'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 418552 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256584 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256584 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsL.

Module LibSegNs_ad_jsRl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [256888].
Definition STOPS1 : list Z := [256888] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1!$9#10,8$29'$29#1000#7??????00000'$22##20000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32"%pstring).
Definition ss0 : sym_state := SS 256828 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>;78#3>;78#5=#3>;78,20#$2<$2$3$4$5$6$7$2=$2>+$22$29$;$<$=$>$?$10$11$2?$30$31$32$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1!$9#10,8$29'$29#1000#7??????00000'$22##20000000!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256828 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256828 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsRl.

Module LibSegNs_ad_jsRs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [256888].
Definition STOPS1 : list Z := [256888] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$2:'$2:##16'&9@#2$2:#1##'$22##16!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32"%pstring).
Definition ss0 : sym_state := SS 256828 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>;78#3>;78#5=#3>;78,20#$2<$2$3$4$5$6$7$2=$2>++$9$22#1$;$<$=$>$?$10$11$2?$30$31$32$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$2:'$2:##16'&9@#2$2:#1##'$22##16!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256828 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256828 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsRs.

Module LibSegNs_ad_jsS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [256772; 418552].
Definition STOPS1 : list Z := [256772; 418552] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$24$22$25+$25$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256584 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3>;04#662?8#3>;04#662?8#5;#3>:;4,20#$1+$2-40$3$4$5$6$7$22$:$26#16+@-1$22#16$22+$25$24$?$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3>;04#662?8#3>;04#662?8#5=#662?8,20##3>:<<+$2-40$3$4$5$6$7$22$:$:#16++$22$24-16$22$22#$24$11$25+$24$25+$22$24$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4+@-1$22#16$24#1#1!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#3>;04#662?8#3>;04#662?8#5=#3>;04,20#$1+$2-40$3$4$5$6$7$22$:##16+@-1$22#16$22+$25$24$?$24$11$25+$24$25+$22$24+$:#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4+@-1$22#16$24##!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18!$:#,1@#2$22'$22##16'&9@#2$22#1##!$:#,8$26'&9$26#1##'$24#1#20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256772 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 418552 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256584 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256584 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsS.

End BndP_Ns_033.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_002.
Module BndP_Ns_034.
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
Ltac2 kr_t_BndP_Ns_034 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_652f5f2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTl3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034@LibSegNs_ad_jsTs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_jsTs23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_79379f2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_jwS3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_ef60e12ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA012BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA013NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA012BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA015XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA012F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA013PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA014planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA015regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA013kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA112BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA113NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA112BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA115XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA112F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA113PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA114planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA115regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA113kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA202BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA203NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA202BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA205XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA202F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA203PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA204planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA205regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA203kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA212BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA213NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA212BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA215XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA212F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA213PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA214planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA215regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlA213kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034?LibSegNs_ad_nlC3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_59a8582ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034ALibSegNs_ad_nlEd23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0L3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk0S3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_034BLibSegNs_ad_nlEk1L3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ad_jsTl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24$29$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1'$22##20000000'$24#1#20000000'$29#1000#7??????00000(+$29+$22$24##1)+$29+$22$24##1$9##18)$2-40#40+$29+$22$24##1'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (8), ELit 8); ((EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 9), (8), 8); ((EAlu Instr.ALU_ADD (EVar 41) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##3>;3<+$2-40$3$4$5$6$7$22$9+$22$29$25$24$=$>$?$10$11$25+$25$24+$22+$24$29$29$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!+$22+$24$29#,1#!$9#8,8+$22$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1$21'$21##??'&9$21#1#1#1'$22##20000000'$24#1#20000000'$29#1000#7??????00000(+$29+$22$24##1)+$29+$22$24##1$9##18)$2-40#40+$29+$22$24##1'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsTl.

Module LibSegNs_ad_jsTs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$22'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 9), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##3>;3<+$2-40$3$4$5$6$7$22$9++$9$22#1$25$24$=$>$?$10$11$25+$25$24++$9+$22$24#1+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!+$9+$22$24#1,1#!$9#,1+@#2$22@#2$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsTs.

Module LibSegNs_ad_jsTs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_652f5f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_652f5f.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$22$9$:$;$<$=$>$?$10$11$25+$25$24+$22$24+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18!$9#,1@#2$22'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256772 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 9), (0), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 9) (ELit 1)) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 9), (0), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 9) (ELit 1)) (EAlu Instr.ALU_ADD (EVar 34) (EVar 36))), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##3>;3<+$2-40$3$4$5$6$7$22$9++$9$22#1$25$24$=$>$?$10$11$25+$25$24++$9+$22$24#1+$9#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,?!+$9+$22$24#1,1#!$9#,1+@#2$22@#2$24'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$22##16'&9@#2$22#1##'$24#1#16'+$22$24#1#16'$25##800000000000'+$25$24##800000000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_652f5f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256772 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_652f5f.IT BndT_Ns_001.SegItab_Ns_652f5f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256772 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jsTs2.

Module LibSegNs_ad_jwL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_79379f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_79379f.IT.
Definition ENDS : list Z := [256540; 256584; 256372].
Definition STOPS1 : list Z := [256540; 256584; 256372] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$23+$27$22$25+$25$24$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256264 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5;#3>940,20#$1+$2-40$3$4$5$6$7$24$23$27+$27$22$21$25+$24$25#1$10$11+$22$27$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5=#3>:1<,20#$1$2$3$4$5$6$7$8$9+$22$27+$27$22$21$25+$24$25#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16'&4&1$24##1#1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5;#3>964,20#$1+$2-40$3$4$5$6$7$24$23$27+$27$22$22$25+$24$25#1$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5=#3>:48,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4$25$27#1#1'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5;#3>970,20#$1+$2-40$3$4$5$6$7$24$23++$22$27#1+$27$22$22$25+$24$25#1$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,17'&4$25$27##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5:#3>974,20#$1+$2-40$3$4$5$6$7$24$23++$22$27#1+$27$22$22$25+$24$25#1$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'&4$25++$22$27#1#1#1'&4$25$27##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5=#3>:48,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#1$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'&4$25++$22$27#1##'&4$25$27##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1$21'$21##??'&9$21#1#1#1!$23#8,8$22'$22##20000000!$23#10,8$27'$27#1000#7??????00000'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 3)) (SGA.mkplan (fst ex10) (SGP.PEnd 2))))))).
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
Definition ps0 : SR.post_spec := SR.PS 256540 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 256584 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 256584 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s9).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s9).
Definition ps3 : SR.post_spec := SR.PS 256372 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_79379f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256264 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_79379f.IT BndT_Ns_001.SegItab_Ns_79379f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jwL.

Module LibSegNs_ad_jwS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_79379f.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_79379f.IT.
Definition ENDS : list Z := [256540; 256584; 256372].
Definition STOPS1 : list Z := [256540; 256584; 256372] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$23+$23+$22#1$25+$25$24$24$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000"%pstring).
Definition ss0 : sym_state := SS 256264 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5;#3>94<,20#$1+$2-40$3$4$5$6$7$24$23+$23#1+$23+$22#1@#2$22$25+$24$25#$10$11++$22$23#1$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5=#3>:1<,20#$1$2$3$4$5$6$7$8$9++$22$23#1+$23+$22#1@#2$22$25+$24$25#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'&4&1$24##1#1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5;#3>964,20#$1+$2-40$3$4$5$6$7$24$23+$23#1+$23+$22#1$22$25+$24$25#$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5=#3>:48,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'&4$25+$23#1#1#1'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5;#3>970,20#$1+$2-40$3$4$5$6$7$24$23++$22$23#2+$23+$22#1$22$25+$24$25#$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'&4$25+$23#1##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5:#3>974,20#$1+$2-40$3$4$5$6$7$24$23++$22$23#2+$23+$22#1$22$25+$24$25#$10$11$22$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4$25++$22$23#2#1#1'&4$25+$23#1##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#3>:1<#3>:48#3>974#3>:1<#3>:48#3>974#5=#3>:48,20#$1$2$3$4$5$6$7$8$9$23$24$22$25+$24$25#$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4$25++$22$23#2##'&4$25+$23#1##'&4&1$24##1##!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#7???7?800040#7?????????>8&$23#8)$2-40#40$23##18($23##18!$23#,1@#2$22'$22##16'&9@#2$22#1##'$24##20000000'$25##800000000000'+$25$24##800000000000,40!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 3)) (SGA.mkplan (fst ex10) (SGP.PEnd 2))))))).
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
Definition ps0 : SR.post_spec := SR.PS 256540 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 256584 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s10).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s10).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s10 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s10 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s10).
Definition ps2 : SR.post_spec := SR.PS 256584 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s9).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s9).
Definition ps3 : SR.post_spec := SR.PS 256372 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_79379f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 256264 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_79379f.IT BndT_Ns_001.SegItab_Ns_79379f.IT_sound BF NX0 BR XSTEP F0 PSS plan 256264 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_jwS.

Module LibSegNs_ad_nlA01.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [243344].
Definition STOPS1 : list Z := [243344] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#!$25-10,4#1,$25-8#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 243272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;690#3;690#5=#3;690,20#$28$2$3$4$5$6$7$29$2:#1#1##2$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$25-8,8+$40#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#!$25-10,4#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,41!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 243344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 243272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 243272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlA01.

Module LibSegNs_ad_nlA11.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [243344].
Definition STOPS1 : list Z := [243344] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#1!$25-10,4#1,$25-8#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 243272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;690#3;690#5=#3;690,20#$28$2$3$4$5$6$7$29$2:#1#1#1#2$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$25-8,8+$40#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#1!$25-10,4#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,41!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 243344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 243272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 243272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlA11.

Module LibSegNs_ad_nlA20.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [243344].
Definition STOPS1 : list Z := [243344] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#2!$25-10,4#,$25-8#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 243272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;690#3;690#5=#3;690,20#$28$2$3$4$5$6$7$29$2:#1#1#2#2$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$25-10,4#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#2,$25-8#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 243344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 243272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 243272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlA20.

Module LibSegNs_ad_nlA21.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [243344].
Definition STOPS1 : list Z := [243344] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#2!$25-10,4#1,$25-8#8!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 243272 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 37), (-8), ELit 8); ((EVar 37), (-16), ELit 4)].
Definition F0L : list SR.region := [((EVar 37), (-8), 8); ((EVar 37), (-16), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;690#3;690#5=#3;690,20#$28$2$3$4$5$6$7$29$2:#1##2#2$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$25-10,4#!$25-8,8+$40#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-14,4#2!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,41!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 243344 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 243272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 243272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlA21.

Module LibSegNs_ad_nlC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24+$24#30$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 243260 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3;648+$2-40$3$4$5$6$7$24+$24#30+$24#30#3:$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 243260 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 243260 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlC.

Module LibSegNs_ad_nlEd2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_59a858.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_59a858.IT.
Definition ENDS : list Z := [264248].
Definition STOPS1 : list Z := [264248] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18$26##38)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#!$25-10,4#1'$26#7???7?800040#7?????????<8)$2-40#40$26##38)$24##60$26##38!$26#,8#;?>30!$24#10,8$26%#10000#<6<<0"%pstring).
Definition ss0 : sym_state := SS 242724 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40838#40838#5=#40838,20##3;52<+$2-40$3$4$5$6$7$24$=$26$;$<$=#40838$?$10$11$<$;$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18$26##38)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#!$25-10,4#1'$26#7???7?800040#7?????????<8)$2-40#40$26##38)$24##60$26##38!$26#,8#;?>30!$24#10,8$26%#10000#<6<<0,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264248 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_59a858.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242724 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_59a858.IT BndT_Ns_001.SegItab_Ns_59a858.IT_sound BF NX0 BR XSTEP F0 PSS plan 242724 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlEd2.

Module LibSegNs_ad_nlEk0L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [256264].
Definition STOPS1 : list Z := [256264] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-10,4#%#10000#<6<<0!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000"%pstring).
Definition ss0 : sym_state := SS 242724 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 48), (0), ELit 1); ((EVar 36), (32), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 48), (0), 1); ((EVar 36), (32), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>908#3>908#5=#3>908,20##3;4;8+$2-40$3$4$5$6$7$24$=+$24#18$30#10><9#10><=#4$?$10$11$<$;$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!$24#20,8#!$30#,1#!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25%#10000#<6<<0!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242724 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 242724 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlEk0L.

Module LibSegNs_ad_nlEk0S.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [256264].
Definition STOPS1 : list Z := [256264] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-10,4#%#10000#<6<<0!$24#18,1@#2$2='$2=##16'&9@#2$2=#1##"%pstring).
Definition ss0 : sym_state := SS 242724 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 36), (24), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 36), (24), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>908#3>908#5=#3>908,20##3;4;8+$2-40$3$4$5$6$7$24$=+$24#18+$24#19#10><9#10><=#4$?$10$11$<$;$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$24#18,2#!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-10,4#%#10000#<6<<0'$2=##16'&9@#2$2=#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242724 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 242724 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlEk0S.

Module LibSegNs_ad_nlEk1L.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [256264].
Definition STOPS1 : list Z := [256264] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-10,4#1%#10000#<6<<0!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#20,8$2?!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000"%pstring).
Definition ss0 : sym_state := SS 242724 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 48), (0), ELit 1); ((EVar 36), (32), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 48), (0), 1); ((EVar 36), (32), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3>908#3>908#5=#3>908,20##3;4;8+$2-40$3$4$5$6$7$24$=+$24#18$30#10><9#10><=#4$?$10$11$<$;$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,20!$24#20,8#!$30#,1#!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25%#10000#<6<<0!$24#18,1$2>'$2>##??'&9$2>#1#1#1!$24#28,8$30'$2?##80000000'$30#1000#7??????00000($30##1)$2-40#40$30##1)$24##60$30##1)$30##1##10000#>:000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 256264 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242724 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 242724 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlEk1L.

End BndP_Ns_034.
Module BndP_Ns_036.
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
Ltac2 kr_t_BndP_Ns_036 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_59a8582ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlR13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_ef60e12ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036ALibSegNs_ad_nlV1z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_nlV23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_fc57112ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbL03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbLI3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbM3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036@LibSegNs_ad_pbSG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0158;BndP_Ns_036?LibSegNs_ad_pbT3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_ad_nlR1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_59a858.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_59a858.IT.
Definition ENDS : list Z := [243272].
Definition STOPS1 : list Z := [243272] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 242988 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;648#3;648#5=#3;648,20#$1$2$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 243272 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_59a858.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242988 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_59a858.IT BndT_Ns_001.SegItab_Ns_59a858.IT_sound BF NX0 BR XSTEP F0 PSS plan 242988 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlR1.

Module LibSegNs_ad_nlV1n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [418884].
Definition STOPS1 : list Z := [418884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8$27'$27#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 242872 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66444#66444#5=#66444,20##3;4?4+$2-40$3$4$5$6$7$24+$24#30+$24#30#2<#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8$27'$27#1^#?#???????????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 418884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242872 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 242872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlV1n.

Module LibSegNs_ad_nlV1z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [242932].
Definition STOPS1 : list Z := [242932] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8#"%pstring).
Definition ss0 : sym_state := SS 242872 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;4?4#3;4?4#5=#3;4?4,20#$1+$2-40$3$4$5$6$7$24+$24#30##1#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#1!$25-10,4#1!$25-8,8#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 242932 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242872 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 242872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlV1z.

Module LibSegNs_ad_nlV2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ef60e1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ef60e1.IT.
Definition ENDS : list Z := [242932].
Definition STOPS1 : list Z := [242932] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$24$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#2!$25-10,4#1"%pstring).
Definition ss0 : sym_state := SS 242872 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3;4?4#3;4?4#5=#3;4?4,20#$1+$2-40$3$4$5$6$7$24+$24#30$25#2#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800040#800000000000&$2#10($2-40#40'$24#7???7?800040#7?????????:0&$24#8)$2-40#40$24##60($24#18#48'$25#1018#7??????00000&$25#8($25-18#18)$2-40#40$25-18#18)$24##60$25-18#18)$25-18#18##10000#>:000!$24#50,8$25!$25-18,4#1!$25-14,4#2!$25-10,4#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 242932 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ef60e1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 242872 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ef60e1.IT BndT_Ns_002.SegItab_Ns_ef60e1.IT_sound BF NX0 BR XSTEP F0 PSS plan 242872 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_nlV2.

Module LibSegNs_ad_pbD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483136 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64);
   KRange (EVar 35) 13 1073741824].
Definition ss0 : sym_state := SS 419096 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##6652<+$2-40$3$4$5$6$7$8$9$12@#2$23$<$=$>$?$10$11$12$13$14@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#=#40000000,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 419096 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 419096 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbD.

Module LibSegNs_ad_pbF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [419188].
Definition STOPS1 : list Z := [419188] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$8##??'$14##80000000'$13#30#80000000'$16#1000#7??????00000(+$14$16##2)+$14$16##2$9##18)$2-40#40+$14$16##2!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?"%pstring).
Definition ss0 : sym_state := SS 419116 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 9), (0), ELit 24); ((EAlu Instr.ALU_ADD (EVar 20) (EVar 22)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 9), (0), 24); ((EAlu Instr.ALU_ADD (EVar 20) (EVar 22)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66574#66574#5=#66574,20#$28$2$3$4$5$6$7$29$2:+$14$16+$14#1$<$=$>$?$10$11$2;$2<$2=$2>$2?$17$18$19$1:$1;$1<$1=$1>$1?,,1;!+$14$16#1,1#!+$14$16#,1$8!$9#8,8+$14#1!$9#10,8$16!$9#,8+@#2&6$13#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$8##??'$14##80000000'$13#30#80000000'$16#1000#7??????00000(+$14$16##2)+$14$16##2$9##18)$2-40#40+$14$16##2!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 419188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 419116 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 419116 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbF.

Module LibSegNs_ad_pbL0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [419128; 418988].
Definition STOPS1 : list Z := [419128; 418988] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8+@#2$23#1'$23#=#40000000!$:#8,8$22'$22##80000000"%pstring).
Definition ss0 : sym_state := SS 418884 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#66538#664:<#66538#664:<#5;#664:8,20#$1+$2-40$3$4$5$6$7$;$:+@#2$23-1$;$21$=$>$?$10$11$12$13$22@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8+@#2$23#1'$23#=#40000000!$:#8,8$22'$22##80000000,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#66538#664:<#66538#664:<#5:#664:<,20#$1+$2-40$3$4$5$6$7$;$:+@#2$23-1$;$21$=$>$?$10$11$12$13$22@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'&4&1$22+@#2$23-1#1#1#1!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8+@#2$23#1'$23#=#40000000!$:#8,8$22'$22##80000000,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#66538#664:<#66538#664:<#5:#66538,20#$1+$2-40$3$4$5$6$7$;$:+@#2$23-1$;$21$=$>$?$10$11$12$13$22@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,18'&4&1$22+@#2$23-1#1##!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1$21'$21##??'&9$21#1#1#1!$:#,8+@#2$23#1'$23#=#40000000!$:#8,8$22'$22##80000000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 419128 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 418988 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 418884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbL0.

Module LibSegNs_ad_pbLG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9+@#2$23-1$;$<$=$>$?$10$11$12$13+@#2$23-1@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$23#=#40000000!$9#10,8$25"%pstring).
Definition ss0 : sym_state := SS 418988 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##66508+$2-40$3$4$5$6$7$8$9+@#8&6+@#4$23-2#3#8#<$<$=$>$?$10$11$25+@#8&6+@#4$23-2#3#8+@#2$23-1@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$23#=#40000000!$9#10,8$25,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418988 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 418988 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbLG.

Module LibSegNs_ad_pbLI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [419188].
Definition STOPS1 : list Z := [419188] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$8##??'$14##80000000!$9#10,8$25'$25#1000#7??????00000(+$14$25##2)+$14$25##2$9##18)$2-40#40+$14$25##2!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?"%pstring).
Definition ss0 : sym_state := SS 419128 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 9), (8), ELit 8); ((EAlu Instr.ALU_ADD (EVar 20) (EVar 37)), (0), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 9), (8), 8); ((EAlu Instr.ALU_ADD (EVar 20) (EVar 37)), (0), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66574#66574#5=#66574,20#$28$2$3$4$5$6$7$29$2:+$14$25+$14#1$<$=$>$?$10$11$2;$2<$2=$2>$2?$17$18$19$1:$1;$1<$1=$1>$1?,,19!+$14$25#1,1#!+$14$25#,1$8!$9#8,8+$14#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$9#7???7?800040#7?????????>8&$9#8)$2-40#40$9##18($9##18'$8##??'$14##80000000!$9#10,8$25'$25#1000#7??????00000(+$14$25##2)+$14$25##2$9##18)$2-40#40+$14$25##2!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 419188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 419128 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 419128 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbLI.

Module LibSegNs_ad_pbM.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [761212].
Definition STOPS1 : list Z := [761212] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483136 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 419080 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9=7<#;9=7<#5=#;9=7<,20##66518+$2-40$3$4$5$6$7$8$9$:$12$14$=$>$?$10$11$12$13$14$15$:$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800040#800000000000&$2#10($2-40#40,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 419080 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 419080 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbM.

Module LibSegNs_ad_pbS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [419188].
Definition STOPS1 : list Z := [419188] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1@#2$22'$22##15'&9@#2$22#1##"%pstring).
Definition ss0 : sym_state := SS 418884 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 10), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 10), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66574#66574#5=#66574,20#$1$2$3$4$5$6$7$8$9++$:$22#1$;+@#2$22#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!+$:$22#2,1#!+$:$22#1,1$;!$:#,1+@#2$22#2!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??'$22##15'&9@#2$22#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 419188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 418884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbS.

Module LibSegNs_ad_pbS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [419188].
Definition STOPS1 : list Z := [419188] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1@#2$22'$22##15'&9@#2$22#1##"%pstring).
Definition ss0 : sym_state := SS 418884 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 10), (0), ELit 1); ((EAlu Instr.ALU_ADD (EVar 10) (EVar 34)), (1), ELit 2)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 10), (0), 1); ((EAlu Instr.ALU_ADD (EVar 10) (EVar 34)), (1), 2)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#66574#66574#5=#66574,20#$1$2$3$4$5$6$7$8$9++$:$22#1$;+@#2$22#2$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!+$:$22#2,1#!+$:$22#1,1$;!$:#,1+@#2$22#2!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??'$22##15'&9@#2$22#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 419188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 418884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbS2.

Module LibSegNs_ad_pbSG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1#2<"%pstring).
Definition ss0 : sym_state := SS 418884 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##66508+$2-40$3$4$5$6$7$;$:#30$;#2<$=$>$?$10$11+$:#1#30#16#17$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800040#7?????????>8&$:#8)$2-40#40$:##18($:##18'$;##??!$:#,1#2<,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 418884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 418884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbSG.

Module LibSegNs_ad_pbT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc5711.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc5711.IT.
Definition ENDS : list Z := [419116].
Definition STOPS1 : list Z := [419116] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14#17$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483136 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 419096 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6652<#6652<#5=#6652<,20#$1+$2-40$3$4$5$6$7$8$9#17$;$<$=$>$?$10$11$12$13$14#17$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?800040#800000000000&$2#10($2-40#40,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 419116 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc5711.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 419096 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc5711.IT BndT_Ns_002.SegItab_Ns_fc5711.IT_sound BF NX0 BR XSTEP F0 PSS plan 419096 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_ad_pbT.

End BndP_Ns_036.
