(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002 BndT_Ns_000. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Ns_045.
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
Ltac2 kr_t_BndP_Ns_045 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bd67f12ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045?LibSegNs_enEOp23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045@LibSegNs_enEOp2w3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045>LibSegNs_enEOr3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_d4c16a2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_erB3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_2be9802ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045=LibSegNs_fbB23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_fbE3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_28e5332ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_045<LibSegNs_hnD3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_enEOp1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bd67f1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bd67f1.IT.
Definition ENDS : list Z := [264020].
Definition STOPS1 : list Z := [264020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:+$26#18$<$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#7?????????>8&$26#8!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264024 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40754#40754#5=#40754,20#$2<$2$3$4$5$6$7$2=$2>#1+$26#18$26$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$:#20,8$26'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#7?????????>8&$26#8!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 264020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bd67f1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bd67f1.IT BndT_Ns_002.SegItab_Ns_bd67f1.IT_sound BF NX0 BR XSTEP F0 PSS plan 264024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEOp1.

Module LibSegNs_enEOp2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bd67f1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bd67f1.IT.
Definition ENDS : list Z := [264020].
Definition STOPS1 : list Z := [264020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$27$<$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38!$27-20,8$2?'$2?#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264024 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40754#40754#5=#40754,20#$2<$2$3$4$5$6$7$2=$2>#1$27+$27-18$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$27-20,8+$2?#1!$:#20,8+$27-18'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38'$2?#^#?#??????????????>!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 264020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bd67f1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bd67f1.IT BndT_Ns_002.SegItab_Ns_bd67f1.IT_sound BF NX0 BR XSTEP F0 PSS plan 264024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEOp2.

Module LibSegNs_enEOp2w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bd67f1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bd67f1.IT.
Definition ENDS : list Z := [264020].
Definition STOPS1 : list Z := [264020] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8$9$:$27$<$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38!$27-20,8^#?#???????????????!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264024 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40754#40754#5=#40754,20#$2<$2$3$4$5$6$7$2=$2>#1$27+$27-18$26$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13!$27-20,8#!$:#20,8+$27-18'$2#7???7?800030#7?????????<0&$2#10($2-30#30'$:#7???7?800000#7?????????<8&$:#8($:##38)$2-30#30$:##38'$26#1000#800000000000'$27#1030#800000000000&$27#8'+$27@-1$26#30#186:0($27-30#30)$27-30#30$2-30#30)$27-30#30$:##38!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 264020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bd67f1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264024 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bd67f1.IT BndT_Ns_002.SegItab_Ns_bd67f1.IT_sound BF NX0 BR XSTEP F0 PSS plan 264024 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEOp2w.

Module LibSegNs_enEOr.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bd67f1.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bd67f1.IT.
Definition ENDS : list Z := [264020].
Definition STOPS1 : list Z := [264020] ++ ENDS.
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
Definition ss0 : sym_state := SS 264000 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40754#40754#5=#40754,20#$2<$2$3$4$5$6$7$2=$2>#1$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'$2#7???7?800030#7?????????<0&$2#10($2-30#30!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 264020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bd67f1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264000 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bd67f1.IT BndT_Ns_002.SegItab_Ns_bd67f1.IT_sound BF NX0 BR XSTEP F0 PSS plan 264000 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_enEOr.

Module LibSegNs_erA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_d4c16a.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_d4c16a.IT.
Definition ENDS : list Z := [268968].
Definition STOPS1 : list Z := [268968] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800080#800000000000&$2#10($2-80#80'$21#7???7?800080#7??????????0&$21#8)$2-80#80$21##10($21##10'$22#1#40!##=6>50,1#1"%pstring).
Definition ss0 : sym_state := SS 268884 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((EVar 33), (0), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((EVar 33), (0), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41::8#41::8#5=#41::8,20#$1$2$3$4$5$6$7$8$9$21$22$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>!$21#8,8#<6;10!$21#,8$22!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-80#80'$21#7???7?800080#7??????????0&$21#8)$2-80#80$21##10($21##10'$22#1#40!##=6>50,1#1,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 268968 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_d4c16a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 268884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_d4c16a.IT BndT_Ns_002.SegItab_Ns_d4c16a.IT_sound BF NX0 BR XSTEP F0 PSS plan 268884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_erA.

Module LibSegNs_erB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_d4c16a.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_d4c16a.IT.
Definition ENDS : list Z := [268968].
Definition STOPS1 : list Z := [268968] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 34; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800080#800000000000&$2#10($2-80#80'$21#7???7?800080#7??????????0&$21#8)$2-80#80$21##10($21##10'$22#1#40%#10000#<6<<0%#=6>50#=6>52(##=6>50#2%#?8898#?88:0!##?88:0,4#1%#?88:4#?88:8!##?88:8,8#?88;0%#?88;0#?88;8%#?88<0#?89;8%#?89<0#?8:;8(##?8898#220%#?8:>3#?8:>4"%pstring).
Definition ss0 : sym_state := SS 268884 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-128), ELit 128); ((EVar 33), (0), ELit 16); ((ELit 0), (880208), ELit 2); ((ELit 0), (1018016), ELit 4); ((ELit 0), (1018048), ELit 8); ((ELit 0), (1018304), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-128), 128); ((EVar 33), (0), 16); ((ELit 0), (880208), 2); ((ELit 0), (1018016), 4); ((ELit 0), (1018048), 8); ((ELit 0), (1018304), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41::8#41::8#5=#41::8,20#$1$2$3$4$5$6$7$8$9$21#1#8#$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,22!$21#8,8#<6;10!$21#,8$22!##=6>51,1#1!##=6>50,1#1!##?88:0,4#2!##?89<0,8#<6;10!##?88<0,8#6553<!$2-50,8$14!$2-48,8$13!$2-40,8$12!$2-38,8$22!$2-30,8$21!$2-28,8#41:=<!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-80#80'$21#7???7?800080#7??????????0&$21#8)$2-80#80$21##10($21##10'$22#1#40%#10000#<6<<0(##=6>50#2%#?8898#?88:0%#?88:4#?88:8!##?88:8,8#?88;0%#?88;0#?88;8%#?88<8#?89;8%#?89<8#?8:;8(##?8898#220%#?8:>3#?8:>4,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 268968 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_d4c16a.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 268884 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_d4c16a.IT BndT_Ns_002.SegItab_Ns_d4c16a.IT_sound BF NX0 BR XSTEP F0 PSS plan 268884 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_erB.

Module LibSegNs_fbA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2be980.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2be980.IT.
Definition ENDS : list Z := [440916].
Definition STOPS1 : list Z := [440916] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#!$25#9<,4#!$25#:0,8+$25#10"%pstring).
Definition ss0 : sym_state := SS 291092 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6;:54#6;:54#5=#6;:54,20##47160+$2-20$3$4$5$6$7$24$9+$25#10$;$<#6;:54$>$?$10$11$<$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#!$25#9<,4#!$25#:0,8+$25#10,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 440916 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2be980.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291092 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2be980.IT BndT_Ns_000.SegItab_Ns_2be980.IT_sound BF NX0 BR XSTEP F0 PSS plan 291092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_fbA.

Module LibSegNs_fbB1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2be980.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2be980.IT.
Definition ENDS : list Z := [291296].
Definition STOPS1 : list Z := [291296] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$24$9#4000$;$<$=$>$?$10$11#4000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#!$25#9<,4#!$25#:0,8+$25#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;"%pstring).
Definition ss0 : sym_state := SS 291168 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#471>0#471>0#5=#471>0,20#$28$2$3$4$5$6$7$29$2:#4000$;$<$=$>$?$10$11$2;$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#!$25#9<,4#!$25#:0,8+$25#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2be980.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291168 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2be980.IT BndT_Ns_000.SegItab_Ns_2be980.IT_sound BF NX0 BR XSTEP F0 PSS plan 291168 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_fbB1.

Module LibSegNs_fbB2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2be980.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2be980.IT.
Definition ENDS : list Z := [291296].
Definition STOPS1 : list Z := [291296] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$24$9$23$;$<$=$>$?$10$11#4000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#!$25#9<,4#!$25#:0,8+$25#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;'$23##3???($25#98#4"%pstring).
Definition ss0 : sym_state := SS 291168 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((EVar 37), (152), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((EVar 37), (152), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#471>0#471>0#5=#471>0,20#$28$2$3$4$5$6$7$29$2:$23#2##$>$?$10$11$2;$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,18!$25#98,4#2'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#9<,4#!$25#:0,8+$25#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;'$23##3???($25#98#4,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2be980.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291168 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2be980.IT BndT_Ns_000.SegItab_Ns_2be980.IT_sound BF NX0 BR XSTEP F0 PSS plan 291168 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_fbB2.

Module LibSegNs_fbE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_2be980.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_2be980.IT.
Definition ENDS : list Z := [291296].
Definition STOPS1 : list Z := [291296] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#2!$25#9<,4#!$25#:0,8+$25#10"%pstring).
Definition ss0 : sym_state := SS 291092 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#471>0#471>0#5=#471>0,20#$1$2$3$4$5$6$7$8$9#$;#78$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800020#800000000000&$2#10($2-20#20'$24#7???7?800020#7????????>=8&$24#8)$2-20#20$24##128'$25#7???7?800020#7????????>?0&$25#8)$2-20#20$25##110%#10000#<6<<0)$24##128$25##110!$24#?0,8$25!$24#?8,8+$25#10!$25#,8#<3688!$25#10,8#<3598!$25#98,4#2!$25#9<,4#!$25#:0,8+$25#10,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291296 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_2be980.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291092 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_2be980.IT BndT_Ns_000.SegItab_Ns_2be980.IT_sound BF NX0 BR XSTEP F0 PSS plan 291092 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_fbE.

Module LibSegNs_hnA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [234216].
Definition STOPS1 : list Z := [234216] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 233676 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#392>8#392>8#5=#392>8,20##390>8+$2-3:0$3$4$5$6$7$8$9+$2-28$:$;$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5!$2-10,8$8!$2-8,8$1'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234216 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233676 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnA.

Module LibSegNs_hnB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [234400].
Definition STOPS1 : list Z := [234400] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 233704 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#393:0#393:0#5=#393:0,20##390?8+$2-3:0$3$4$5$6$7$8$9+$2-138+$2-28#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233704 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnB.

Module LibSegNs_hnC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [234672].
Definition STOPS1 : list Z := [234672] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 233720 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-336), ELit 24); ((EVar 2), (-392), ELit 16); ((EVar 2), (-376), ELit 4); ((EVar 2), (-368), ELit 24); ((EVar 2), (-344), ELit 4); ((EVar 2), (-920), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-336), 24); ((EVar 2), (-392), 16); ((EVar 2), (-376), 4); ((EVar 2), (-368), 24); ((EVar 2), (-344), 4); ((EVar 2), (-920), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#394;0#394;0#5=#394;0,20##39168+$2-3:0$3$4$5$6$7$8$9+$2-380+$2-138+$2-188+$2-398+$2-399$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-388,4#400!$2-384,4#!$2-390,8#;?:30!$2-398,8#;?:08!$2-170,8#!$2-178,4#400!$2-180,8+$2-150!$2-188,8#;?>30!$2-158,4#!$2-160,8#!$2-168,8#!$2-140,8#!$2-148,8#!$2-150,8#'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234672 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233720 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233720 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnC.

Module LibSegNs_hnD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [436020].
Definition STOPS1 : list Z := [436020] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 233832 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-920), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-920), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6:734#6:734#5=#6:734,20##39170+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4!$2-398,4#'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 436020 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233832 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233832 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnD.

End BndP_Ns_045.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000.
Module BndP_Ns_047.
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
Ltac2 kr_t_BndP_Ns_047 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_32460c2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icA3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_icB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047?LibSegNs_icCl1b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCl43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047>LibSegNs_icCs23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_0dae172ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_liA3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_3454c52ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047=LibSegNs_lpAe3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_047<LibSegNs_lpE3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_icA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [590012].
Definition STOPS1 : list Z := [590012] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21$27#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0"%pstring).
Definition ss0 : sym_state := SS 234400 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 208); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-208), 208); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#900;<#900;<!$!!,2#900;<#900;<#5=#900;<,20##39428+$2-50$3$4$35$36$37$21+$21$27+$21#:8$39$3:$3;$3<$3=$3>$3?#8+$21#10+$21#78#<36<0#<36;0#<3670$18$19$1:$1;$40$41$42$43,,20#$21#;0#50!$21#98,4#!$21#90,8#!$21#88,8#6!$21#80,4#1002!$21#:0,8+$21#10!$21#9<,4#!$2-60,8$21!$2-58,8#39428!$21#8,8#!$21#78,8#<3720!$21#,8#<36?8!$21#:8,8#!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0,44!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 590012 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 234400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icA.

Module LibSegNs_icB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [590012].
Definition STOPS1 : list Z := [590012] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$21+$21$27$:$;$<$=$>$?$10$11#8+$21#10+$21#78#<36<0#<36;0#<3670$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0"%pstring).
Definition ss0 : sym_state := SS 234536 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 64); ((EVar 33), (0), ELit 8); ((EVar 33), (16), ELit 8); ((EVar 33), (120), ELit 8); ((EVar 33), (256), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-144), 64); ((EVar 33), (0), 8); ((EVar 33), (16), 8); ((EVar 33), (120), 8); ((EVar 33), (256), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#900;<#900;<#5=#900;<,20##3?;04+$2-90$3$4$5$6$7+$21#10+$21#18+$21#18+$21$27#8$=$>$?$10$11#8#8+$21$27#<3518#<36;0#<3688$18$19$1:$1;$1<$1=$1>$1?,,19!$21#10,8#<3518!$2-88,8#<36<0!$2-80,8+$21#78!$2-78,8+$21#10!$2-70,8#8!$2-68,8+$21$27!$2-60,8$21!$2-58,8#3945<!$21#78,8#<36;0!$21#,8#<3688!$21#10:,1^#?#???????????????!$21#109,1^#?#???????????????!$21#108,1^#?#???????????????!$21#100,8#!$21#10;,1^#?#???????????????'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 590012 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234536 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 234536 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icB.

Module LibSegNs_icCl1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11$12#8+$21$27#<3518$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0!+$21$27#,1$26'$26##??'&9$26#1#1#1!+$21$27#8,8$28!+$21$27#10,8$24'$28#17#2<"%pstring).
Definition ss0 : sym_state := SS 260868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 33), (16), ELit 8); ((EVar 33), (32), ELit 84)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 33), (16), 8); ((EVar 33), (32), 84)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#;>8;0#;>8;0!$!!,2#;>8;0#;>8;0#5=#;>8;0,20##66960+$2-<0$3$4$35$36$37$28+$21#50#30#2<#1>##1$3=$3>$3?+$21#50$24#2?#<3518$16$17$18$19$1:$1;$40$41$42$43,,1:!$2-<0,8+$21$27!$2-;8,8#8!$2-;0,8+$21#50!$2-:8,8+$21#18!$2-:0,8+$21#10!$2-98,8#3?;48!$21#70,4#8!$21#68,8#!$21#60,8#!$21#58,8#!$21#50,8#!$21#10,8#<3598#$21#20#30'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0'$26##??'&9$26#1#1#1'$28#17#2<,44!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 260868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 260868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCl1a.

Module LibSegNs_icCl1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11$12#8+$21$27#<3518$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0!+$21$27#,1$26'$26##??'&9$26#1#1#1!+$21$27#8,8$28!+$21$27#10,8$24'$28#2=#3??????'&8$28#7#2?#4000007"%pstring).
Definition ss0 : sym_state := SS 260868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 48); ((EVar 33), (16), ELit 8); ((EVar 33), (32), ELit 84)].
Definition F0L : list SR.region := [((EVar 2), (-192), 48); ((EVar 33), (16), 8); ((EVar 33), (32), 84)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#;>8;0#;>8;0!$!!,2#;>8;0#;>8;0#5=#;>8;0,20##66960+$2-<0$3$4$35$36$37$28+$21#50+@#8&6$28#3#8#2<#1>##1$3=$3>$3?+$21#50$24+@#8&6$28#3#7#<3518$16$17$18$19$1:$1;$40$41$42$43,,1;!$2-<0,8+$21$27!$2-;8,8#8!$2-;0,8+$21#50!$2-:8,8+$21#18!$2-:0,8+$21#10!$2-98,8#3?;48!$21#70,4#8!$21#68,8#!$21#60,8#!$21#58,8#!$21#50,8#!$21#10,8#<3598#$21#20#30'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0'$26##??'&9$26#1#1#1'$28#2=#3??????'&8$28#7#2?#4000007,44!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 260868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 260868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCl1b.

Module LibSegNs_icCl2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$28$9$29$;$<$=$>$?$10$11$12$24$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 420192 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##66970+$2-<0$3$4$5$6$7$28$9$29$24$28$=$>$?$10$11$29$24$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 760184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 420192 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 420192 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCl2.

Module LibSegNs_icCl3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [260936].
Definition STOPS1 : list Z := [260936] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7$28+$21#50$:$;$<$=$>$?$10$11$29$13$2:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-98,8#3?;48!$2-:0,8+$21#10!$2-:8,8+$21#18!$2-;0,8+$21#50!$2-;8,8#8!$2-<0,8+$21$27'$29#1000#800000000000'$28#17#3??????'$2:#2?#4000007(+$29$28##1)$2-=0#=0+$29$28##1)$21##110+$29$28##1"%pstring).
Definition ss0 : sym_state := SS 420208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (80), ELit 24); ((EAlu Instr.ALU_ADD (EVar 41) (EVar 40)), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (80), 24); ((EAlu Instr.ALU_ADD (EVar 41) (EVar 40)), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3?;48#3?;48#5=#3?;48,20##3?;48+$2-90$3$4$5$6$7+$21#10+$21#18+$21#50$;$<$=$>$?$10$11+$21#50#8+$21$27$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!+$28$29#,1#!$21#60,8$29!$21#58,8$28!$21#50,8+$2:#2'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-98,8#3?;48!$2-:0,8+$21#10!$2-:8,8+$21#18!$2-;0,8+$21#50!$2-;8,8#8!$2-<0,8+$21$27'$29#1000#800000000000'$28#17#3??????'$2:#2?#4000007(+$29$28##1)$2-=0#=0+$29$28##1)$21##110+$29$28##1,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 260936 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 420208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 420208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCl3.

Module LibSegNs_icCl4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [234628].
Definition STOPS1 : list Z := [234628] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#3945<!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#<36<0!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##??'&9$26#1#1#1!$21#58,8$28!$21#60,8$29!$21#70,4#8'$29#1000#800000000000'$28#17#3??????"%pstring).
Definition ss0 : sym_state := SS 260936 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 32); ((EVar 33), (32), ELit 24); ((EVar 33), (104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-176), 32); ((EVar 33), (32), 24); ((EVar 33), (104), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#39484#39484#5=#39484,20#$2;$2$3$4$5$6$7$2<$2=##1+$28$29#8$>$?$10$11$2>$2?$30$31$32$33$18$19$1:$1;$1<$1=$1>$1?,,29!$21#68,8+$28$29!$21#30,8+$28$29!$21#28,8$29!$21#20,8$29!$2-;0,8$12!$2-:8,8$9!$2-:0,8+$21#10!$2-98,8#3?;50'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#3945<!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#<36<0!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##??'&9$26#1#1#1!$21#58,8$28!$21#60,8$29!$21#70,4#8'$29#1000#800000000000'$28#17#3??????,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234628 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 260936 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 260936 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCl4.

Module LibSegNs_icCs1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [260936].
Definition STOPS1 : list Z := [260936] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11$12#8+$21$27#<3518$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0!+$21$27#,1$26'$26##??'&9$26#1##!+$21$27#,8$23!+$21$27#8,8$24!+$21$27#10,8$25"%pstring).
Definition ss0 : sym_state := SS 260868 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (16), ELit 8); ((EVar 33), (32), ELit 84)].
Definition F0L : list SR.region := [((EVar 33), (16), 8); ((EVar 33), (32), 84)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#3?;48#3?;48!$!!,2#3?;48#3?;48#5=#3?;48,20##3?;48+$2-90$3$4$35$36$37+$21#10+$21#18+$21#50$23$24##$3=$3>$3?+$21#50#8+$21$27#<3518$16$17$18$19$1:$1;$40$41$42$43,,17!$21#50,8$23!$21#58,8$24!$21#60,8$25!$21#70,4#8!$21#68,8#!$21#10,8#<3598#$21#20#30'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8%#10000#<6<<0!+$21$27#,1$26'$26##??'&9$26#1##!+$21$27#,8$23!+$21$27#8,8$24!+$21$27#10,8$25,44!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 260936 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 260868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 260868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCs1.

Module LibSegNs_icCs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_32460c.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_32460c.IT.
Definition ENDS : list Z := [234628].
Definition STOPS1 : list Z := [234628] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7+$21#10$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#3945<!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#<36<0!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##2<'&9$26#1##!$21#70,4#8"%pstring).
Definition ss0 : sym_state := SS 260936 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-176), ELit 32); ((EVar 33), (32), ELit 24); ((EVar 33), (104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-176), 32); ((EVar 33), (32), 24); ((EVar 33), (104), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#39484#39484#5=#39484,20#$2;$2$3$4$5$6$7$2<$2=##++$21&6$26#1#51#8$>$?$10$11$2>$2?$30$31$32$33$18$19$1:$1;$1<$1=$1>$1?,,25!$21#68,8++$21&6$26#1#51!$21#30,8++$21&6$26#1#51!$21#28,8+$21#51!$21#20,8+$21#51!$2-;0,8$12!$2-:8,8$9!$2-:0,8+$21#10!$2-98,8#3?;50'$2#7???7?8000=0#800000000000&$2#10($2-=0#=0'$21#7???7?8000=0#7????????>?0&$21#8)$2-=0#=0$21##110($21##110'$27#110#800000&$27#8!$2-58,8#3945<!$2-60,8$21!$2-68,8+$21$27!$2-70,8#8!$2-78,8+$21#10!$2-80,8+$21#78!$2-88,8#<36<0!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$21#50,1$26'$26##2<'&9$26#1##!$21#70,4#8,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234628 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_32460c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 260936 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_32460c.IT BndT_Ns_000.SegItab_Ns_32460c.IT_sound BF NX0 BR XSTEP F0 PSS plan 260936 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_icCs2.

Module LibSegNs_liA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_0dae17.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_0dae17.IT.
Definition ENDS : list Z := [590104].
Definition STOPS1 : list Z := [590104] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#<6<<0%#=7082#=77<0(##=7082#73>%#=7>>8#=7?40(##=7>>8#58%#?8:>3#?8:>4%#?8;;8#?8;;<!##?8:<0,8$22"%pstring).
Definition ss0 : sym_state := SS 590012 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-1024), ELit 1024); ((EVar 33), (0), ELit 8); ((ELit 0), (880770), ELit 1854); ((ELit 0), (884456), ELit 88)].
Definition F0L : list SR.region := [((EVar 2), (-1024), 1024); ((EVar 33), (0), 8); ((ELit 0), (880770), 1854); ((ELit 0), (884456), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",40!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118!$!!,2#90118#90118#5=#90118,20#$1$2$3$4$211$212$213$8$9#=7690#=7690$216$217$218$219$21:$21;$12$13$14$15$16$17$18$19$1:$1;$21<$21=$21>$21?,,11>!$21#,8#=7690!##=7281,1#1!##=7280,1#1!##=7278,8#=7690!##=7271,1#1!##=7270,1#1!##=7268,8#=7690!##=77:0,8#=74<8!##=76:8,8#=77:8!$2-110,8$18!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8#=74=0!$2->8,8#1=!$2->0,8#=7690!$2-=8,8#=76:0!$2-=0,8#=74<8!$2-<8,8#89:8<!##=74=0,8#1!##=7?30,4#!##=7?38,8#!##=7?18,8#!$2-144,4#!$2-140,8$22!$2-138,8#1!$2-130,8$14!$2-128,8#=7>>8!$2-120,8+$2-;0!$2-118,8#=7>>8!##=7>><,4#!$2-158,8$19!$2-150,8$18!##=71<0,8^#?#???????????????!##=71<8,4#1>!##=71=0,4#1>!$2-;0,8+$2-:8!$2-:8,8+$2-;8!$2-;8,8#=71<0!$2-:0,8$14!$2-98,8#=7258!$2-90,8#=7260!$2-88,8#<3:?8!$2-80,8#=7690!$2-78,8#873><!##=74<8,8#<52;0!##=7798,8#=74;8!##=74<0,8#1!##=71;0,8^#?#???????????????!##=71;8,4#1=!##=74;8,8#<5228!##=7790,8#=7598!##=75:0,8#1!##=7120,8^#?#???????????????!##=7128,4#1<!##=75:8,8#1=408!##=7598,8#<4:60!##=7788,8#=7580!##=7588,8#1!##=7110,8^#?#???????????????!##=7118,4#1;!##=7590,8#1=408!##=7580,8#<49>8!##=7780,8#=7568!##=7570,8#1!##=7100,8^#?#???????????????!##=7108,4#1:!##=7578,8#<46=8!##=7568,8#<4678!##=7778,8#=7550!##=7558,8#1!##=70?0,8^#?#???????????????!##=70?8,4#19!##=7560,8#<45<8!##=7550,8#<4568!##=7770,8#=74:8!##=74;0,8#1!##=71:0,8^#?#???????????????!##=71:8,4#18!##=74:8,8#<51:8!##=7768,8#=7498!##=74:0,8#1!##=7190,8^#?#???????????????!##=7198,4#17!##=7498,8#<5128!##=7760,8#=7488!##=7490,8#1!##=7180,8^#?#???????????????!##=7188,4#16!##=7488,8#<50:8!##=7758,8#=7478!##=7480,8#1!##=7170,8^#?#???????????????!##=7178,4#15!##=7478,8#<5028!##=7750,8#=7468!##=7470,8#1!##=7160,8^#?#???????????????!##=7168,4#14!##=7468,8#<4=60!##=7748,8#=7458!##=7460,8#1!##=7150,8^#?#???????????????!##=7158,4#13!##=7458,8#<4<;8!##=7740,8#=7448!##=7450,8#1!##=7140,8^#?#???????????????!##=7148,4#12!##=7448,8#<4<10!##=7738,8#=7438!##=7440,8#1!##=7130,8^#?#???????????????!##=7138,4#11!##=7438,8#<4;58!##=7730,8#=7428!##=7430,8#1!##=70>0,8^#?#???????????????!##=70>8,4#10!##=7428,8#<44:0!##=7728,8#=7418!##=7420,8#1!##=70=0,8^#?#???????????????!##=70=8,4#?!##=7418,8#<43<8!##=7720,8#=7408!##=7410,8#1!##=70<0,8^#?#???????????????!##=70<8,4#>!##=7408,8#<42>8!##=7718,8#=73?8!##=7400,8#1!##=70;0,8^#?#???????????????!##=70;8,4#=!##=73?8,8#<41?8!##=7710,8#=7660!##=7668,8#1!##=7368,8^#?#???????????????!##=7370,4#<!##=7688,8#!##=7680,8#!##=7678,8#!##=7670,8#2<0000002>!##=7660,8#<3:08!##=7708,8#=7630!##=7638,8#1!##=7358,8^#?#???????????????!##=7360,4#;!##=7658,8#!##=7650,8#!##=7648,8#!##=7640,2#2<2>!##=7630,8#<39;8!##=7700,8#=73>8!##=73?0,8#1!##=7228,8^#?#???????????????!##=7230,4#:!##=73>8,8#<3>78!##=76?8,8#=73=8!##=73>0,8#1!##=7208,8^#?#???????????????!##=7210,4#9!##=73=8,8#<3=48!##=76?0,8#=73<8!##=73=0,8#1!##=7218,8^#?#???????????????!##=7220,4#8!##=73<8,8#<3=>0!##=76>8,8#=73;8!##=73<0,8#1!##=71?8,8^#?#???????????????!##=7200,4#7!##=73;8,8#<3<;0!##=76>0,8#=7538!##=7540,8#1!##=71>8,8^#?#???????????????!##=71?0,4#6!##=7548,8#1=408!##=7261,1#1!##=7260,1#1!##=7258,8#1=408!$2-<0,8#!##=7538,8#<3958!##=76=8,8#=73:8!##=73;0,8#1!##=71=8,8^#?#???????????????!##=71>0,4#5!##=73:8,8#<3<08!##=76=0,8#=7398!##=73:0,8#1!##=7338,8^#?#???????????????!##=7340,4#4!##=7398,8#<3;38!##=76<8,8#=75;0!##=75;8,8#1!##=7348,8^#?#???????????????!##=7350,4#3!##=75<8,1#!##=75<0,8#187;0!##=75;0,8#<3800!##=76<0,8#=7388!##=7390,8#1!##=70:0,8^#?#???????????????!##=70:8,4#2!##=7388,8#<41;8!##=76;8,8#=7378!##=7380,8#1!##=7090,8^#?#???????????????!##=7098,4#1!##=7378,8#<4178!##=77;2,1#!##=77;0,2#4302!##=76;0,8#=77:8!##=76:0,8#=76;8!##=7698,8#!##=7690,8#<3758!##=77:8,8#1!$2-68,8$13!$2-60,8#=7258!$2-58,8#=7690!$2-50,8#=7270!$2-48,8#8:310!$2-40,8#=7258!$2-38,8#=7280!$2-30,8$21!$2-28,8#90134!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800400#800000000000&$2#10($2-400#400'$21#7???7?800400#7??????????8&$21#8)$2-400#400$21##8($21##8%#10000#<6<<0%#=7082#=7090%#=709<#=70:0%#=70:<#=70;0%#=70;<#=70<0%#=70<<#=70=0%#=70=<#=70>0%#=70><#=70?0%#=70?<#=7100%#=710<#=7110%#=711<#=7120%#=712<#=7130%#=713<#=7140%#=714<#=7150%#=715<#=7160%#=716<#=7170%#=717<#=7180%#=718<#=7190%#=719<#=71:0%#=71:<#=71;0%#=71;<#=71<0%#=71<<#=71=0%#=71=4#=71=8%#=71>4#=71>8%#=71?4#=71?8%#=7204#=7208%#=7214#=7218%#=7224#=7228%#=7234#=7258%#=7262#=7268%#=7272#=7278%#=7282#=7338%#=7344#=7348%#=7354#=7358%#=7364#=7368%#=7374#=7378%#=74=8#=7538%#=75<9#=7630%#=7642#=7648%#=77;3#=77<0(##=7082#73>%#=7>>8#=7>><%#=7>?0#=7?18%#=7?20#=7?30%#=7?34#=7?38(##=7>>8#58%#?8:>3#?8:>4%#?8;;8#?8;;<!##?8:<0,8$22,220!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 590104 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_0dae17.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 590012 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_0dae17.IT BndT_Ns_000.SegItab_Ns_0dae17.IT_sound BF NX0 BR XSTEP F0 PSS plan 590012 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_liA.

Module LibSegNs_lpA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284584; 236668].
Definition STOPS1 : list Z := [284584; 236668] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#2!$35#8,8$36!$35#10,8$37'$37#^#?#??????????????>!$24#<,4$38'$38#1#400!$25#,8#;?:88"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 53), (16), ELit 8); ((EVar 36), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 53), (16), 8); ((EVar 36), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#457:8#39<7<#457:8#39<7<#5;#4563<,20#$1+$2-70$3$4$5$6$7$26$24+$35#18$37$36$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,22'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#2!$35#8,8$36!$35#10,8$37'$37#^#?#??????????????>!$24#<,4$38'$38#1#400!$25#,8#;?:88,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#457:8#39<7<#457:8#39<7<#5=#457:8,20##45670+$2-70$3$4$5$6$7$26$24$24$25$26$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,22!$35#10,8+$37#1'&4$37$36#1#1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#2!$35#8,8$36'$37#^#?#??????????????>!$24#<,4$38'$38#1#400!$25#,8#;?:88,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#457:8#39<7<#457:8#39<7<#5=#39<7<,20##456>0+$2-70$3$4$5$6$7$26$24$25$24$26#39<7<$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,23!$24#<,4+$38-1'&4$37$36##'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#2!$35#8,8$36!$35#10,8$37'$37#^#?#??????????????>'$38#1#400!$25#,8#;?:88,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 236668 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpA.

Module LibSegNs_lpAe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [236668].
Definition STOPS1 : list Z := [236668] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#2!$35#8,8$37!$35#10,8$37!$24#<,4$38'$38#1#400!$25#,8#;?:88"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 36), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#39<7<#39<7<#5=#39<7<,20##456>0+$2-70$3$4$5$6$7$26$24$25$24$26#39<7<$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,21!$24#<,4+$38-1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#2!$35#8,8$37!$35#10,8$37'$38#1#400!$25#,8#;?:88,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 236668 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpAe.

Module LibSegNs_lpC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [239192].
Definition STOPS1 : list Z := [239192] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#178,8$22!$24#180,8+$22#18'$22#1000#7??????00000&$22#8($22##18)$2-70#70$22##18)$24##190$22##18)$26##10$22##18)$25##60$22##18!$22#,4#1!$25#,8#;?:88"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 2); ((EVar 36), (384), ELit 8)].
Definition F0L : list SR.region := [((EVar 36), (8), 2); ((EVar 36), (384), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:658#3:658#5=#3:658,20##456:0+$2-70$3$4$5$6$7$26$24$25#3:658$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,1>!$24#180,8$22!$24#8,2#100'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#178,8$22'$22#1000#7??????00000&$22#8($22##18)$2-70#70$22##18)$24##190$22##18)$26##10$22##18)$25##60$22##18!$22#,4#1!$25#,8#;?:88,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 239192 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpC.

Module LibSegNs_lpE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284156].
Definition STOPS1 : list Z := [284156] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 38; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#9,1#"%pstring).
Definition ss0 : sym_state := SS 284064 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#455?<#455?<#5=#455?<,20#$1+$2-70$3$4$5$6$7$26$24#135>4$25$26$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,1=!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#9,1#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284156 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284064 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpE.

End BndP_Ns_047.
Module BndP_Ns_048.
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
Ltac2 kr_t_BndP_Ns_048 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_3454c52ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpF3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpKe3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpP3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048=LibSegNs_lpQ13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048<LibSegNs_lpV3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_3944582ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048?LibSegNs_mp_baF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048@LibSegNs_mp_baG03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_048ALibSegNs_mp_baGs13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_lpF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284460].
Definition STOPS1 : list Z := [284460] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31!$24#9,1#1"%pstring).
Definition ss0 : sym_state := SS 284320 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4572<#4572<#5=#4572<,20#$28$2$3$4$5$6$7$29$2:#1$;$<$=$>$?$10$11$2;$2<$2=$2>$2?$30$31$19$1:$1;$1<$1=$1>$1?,,1='$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31!$24#9,1#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpF.

Module LibSegNs_lpK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284584; 241060].
Definition STOPS1 : list Z := [284584; 241060] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",22'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#3!$35#8,8$36!$35#10,8$37'$37#^#?#??????????????>!$24#<,4$38'$38#1#400!$25#,8#;?:88"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 53), (0), ELit 4); ((EVar 53), (16), ELit 8); ((EVar 36), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 53), (0), 4); ((EVar 53), (16), 8); ((EVar 36), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#457:8#3:=:4#457:8#3:=:4#5;#45650,20#$1+$2-70$3$4$5$6$7$26$24+$35#18$37$36$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,22'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#3!$35#8,8$36!$35#10,8$37'$37#^#?#??????????????>!$24#<,4$38'$38#1#400!$25#,8#;?:88,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#457:8#3:=:4#457:8#3:=:4#5=#457:8,20##45670+$2-70$3$4$5$6$7$26$24$24$25$26$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,22!$35#10,8+$37#1!$35#,4#4'&4$37$36#1#1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#8,8$36'$37#^#?#??????????????>!$24#<,4$38'$38#1#400!$25#,8#;?:88,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#457:8#3:=:4#457:8#3:=:4#5=#3:=:4,20##456>0+$2-70$3$4$5$6$7$26$24$25$24$26#3:=:4$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,23!$24#<,4+$38-1'&4$37$36##'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#3!$35#8,8$36!$35#10,8$37'$37#^#?#??????????????>'$38#1#400!$25#,8#;?:88,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 241060 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpK.

Module LibSegNs_lpKe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [241060].
Definition STOPS1 : list Z := [241060] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#3!$35#8,8$37!$35#10,8$37!$24#<,4$38'$38#1#400!$25#,8#;?:88"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 36), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3:=:4#3:=:4#5=#3:=:4,20##456>0+$2-70$3$4$5$6$7$26$24$25$24$26#3:=:4$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,21!$24#<,4+$38-1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#3!$35#8,8$37!$35#10,8$37'$38#1#400!$25#,8#;?:88,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 241060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpKe.

Module LibSegNs_lpP.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284156].
Definition STOPS1 : list Z := [284156] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#10,1#!$24#9,1#!$24#180,8+$35#18'$35#1000#7??????00000"%pstring).
Definition ss0 : sym_state := SS 284384 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (8), ELit 1); ((EVar 36), (384), ELit 8)].
Definition F0L : list SR.region := [((EVar 36), (8), 1); ((EVar 36), (384), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#455?<#455?<#5=#455?<,20#$1+$2-70$3$4$5$6$7$26$24#$35$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,17!$24#180,8$35!$24#8,1#1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#10,1#!$24#9,1#'$35#1000#7??????00000,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284156 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284384 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284384 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpP.

Module LibSegNs_lpQ0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284156].
Definition STOPS1 : list Z := [284156] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#9,1#!$26#,4#"%pstring).
Definition ss0 : sym_state := SS 284272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#455?<#455?<#5=#455?<,20#$1+$2-70$3$4$5$6$7$26$24#$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,14'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#9,1#!$26#,4#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284156 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpQ0.

Module LibSegNs_lpQ1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284460].
Definition STOPS1 : list Z := [284460] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31!$26#,4$39'$39#1#40"%pstring).
Definition ss0 : sym_state := SS 284272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4572<#4572<#5=#4572<,20#$28$2$3$4$5$6$7$29$2:$39$;$<$=$>$?$10$11$2;$2<$2=$2>$2?$30$31$19$1:$1;$1<$1=$1>$1?,,1>'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31!$26#,4$39'$39#1#40,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284460 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpQ1.

Module LibSegNs_lpR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284584].
Definition STOPS1 : list Z := [284584] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#!$35#8,8$36!$35#10,8$37"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 53), (0), ELit 4)].
Definition F0L : list SR.region := [((EVar 53), (0), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#457:8#457:8#5=#457:8,20##45670+$2-70$3$4$5$6$7$26$24$24$25$26$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,1=!$35#,4#1'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#8,8$36!$35#10,8$37,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpR.

Module LibSegNs_lpV.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_3454c5.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_3454c5.IT.
Definition ENDS : list Z := [284584].
Definition STOPS1 : list Z := [284584] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$26$24$:$;$<$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#,4#4!$35#8,8$36!$35#10,8$37"%pstring).
Definition ss0 : sym_state := SS 284156 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 53), (0), ELit 4)].
Definition F0L : list SR.region := [((EVar 53), (0), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#457:8#457:8#5=#457:8,20##45670+$2-70$3$4$5$6$7$26$24$24$25$26$=$>$?$10$11$25#4#1#18#100#13944#3$19$1:$1;$1<$1=$1>$1?,,1=!$35#,4#3'$2#7???7?800070#800000000000&$2#10($2-70#70'$24#7???7?800070#7????????>70&$24#8)$2-70#70$24##190'$26#7???7?800070#7??????????0&$26#8)$2-70#70$26##10'$25#7???7?800070#7?????????:0&$25#8)$2-70#70$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#10($24#178#18!$24#8,1#1!$24#180,8+$35#18'$35#1000#7??????00000&$35#8($35##18)$2-70#70$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$35#8,8$36!$35#10,8$37,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284584 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_3454c5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_3454c5.IT BndT_Ns_000.SegItab_Ns_3454c5.IT_sound BF NX0 BR XSTEP F0 PSS plan 284156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_lpV.

Module LibSegNs_mp_baA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [289496].
Definition STOPS1 : list Z := [289496] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 12; EVar 38; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$24#<,4$21'$21##3??!$24#140,4#400($24#<#4"%pstring).
Definition ss0 : sym_state := SS 288316 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46:=8#46:=8#5=#46:=8,20##46690+$2-70$3$4$5$6$7$24$26$24$<$26+$21#1$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$24#<,4+$21#1!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18'$21##3??!$24#140,4#400($24#<#4,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288316 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baA.

Module LibSegNs_mp_baE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [268884].
Definition STOPS1 : list Z := [268884] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 12; EVar 38; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",15'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$24#<,4#400!$24#140,4#400($24#<#4"%pstring).
Definition ss0 : sym_state := SS 288316 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41:54#41:54#5=#41:54,20##467?8+$2-70$3$4$5$6$7$24$26$26#8$<#401$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#<,4#401!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$24#140,4#400($24#<#4,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288316 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288316 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baE.

Module LibSegNs_mp_baF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [288656].
Definition STOPS1 : list Z := [288656] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8$35!$24#188,8+$35$33'$33#18#10000'$35#1000#7??????00000&$35#8($35##18)$2-80#80$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46790#46790#5=#46790,20#$1+$2-70$3$4$5$6$7$24$26#2+$35$33$<$=$>$?$10$11$25$30$14+$35#18$16$17$18$19$1:$1;$1<$1=$1>$1?,,28!$35#10,8#!$35#8,8$30!$35#,4#2'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8$35!$24#188,8+$35$33'$33#18#10000'$35#1000#7??????00000&$35#8($35##18)$2-80#80$35##18)$24##190$35##18)$26##10$35##18)$25##60$35##18!$24#8,1#1,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288656 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baF.

Module LibSegNs_mp_baG0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [288744].
Definition STOPS1 : list Z := [288744] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#8,1#"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#467>8#467>8#5=#467>8,20#$28$2$3$4$5$6$7$29$2:$30#$<$=$>$?$10$11$2;$2<$2=$2>$2?$17$18$19$1:$1;$1<$1=$1>$1?,,1;'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#8,1#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baG0.

Module LibSegNs_mp_baGs0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#18!$24#188,8+$22#18'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#2$26#30#40#1#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#18+$22#18$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#18!$24#188,8+$22#18'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs0.

Module LibSegNs_mp_baGs1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#30!$24#188,8+$22#30'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#4$26#60#80#2#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#30+$22#30$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#30!$24#188,8+$22#30'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs1.

End BndP_Ns_048.
Module BndP_Ns_049.
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
Ltac2 kr_t_BndP_Ns_049 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_3944582ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs102BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs103NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs102BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs105XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs102F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs103PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs104planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs105regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049BLibSegNs_mp_baGs103kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs92BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs93NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs92BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs95XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs92F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs93PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs94planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs95regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049ALibSegNs_mp_baGs93kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baJ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baR3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baT3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baU3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_049?LibSegNs_mp_baZ3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_mp_baGs10.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#6000!$24#188,8+$22#6000'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#800$26#<000#10000#400#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#6000+$22#6000$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#6000!$24#188,8+$22#6000'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs10.

Module LibSegNs_mp_baGs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#60!$24#188,8+$22#60'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#8$26#<0#100#4#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#60+$22#60$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#60!$24#188,8+$22#60'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs2.

Module LibSegNs_mp_baGs3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<0!$24#188,8+$22#<0'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#10$26#180#200#8#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#<0+$22#<0$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<0!$24#188,8+$22#<0'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs3.

Module LibSegNs_mp_baGs4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#180!$24#188,8+$22#180'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#20$26#300#400#10#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#180+$22#180$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#180!$24#188,8+$22#180'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs4.

Module LibSegNs_mp_baGs5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#300!$24#188,8+$22#300'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#40$26#600#800#20#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#300+$22#300$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#300!$24#188,8+$22#300'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs5.

Module LibSegNs_mp_baGs6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#600!$24#188,8+$22#600'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#80$26#<00#1000#40#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#600+$22#600$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#600!$24#188,8+$22#600'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs6.

Module LibSegNs_mp_baGs7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<00!$24#188,8+$22#<00'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#100$26#1800#2000#80#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#<00+$22#<00$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#<00!$24#188,8+$22#<00'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs7.

Module LibSegNs_mp_baGs8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#1800!$24#188,8+$22#1800'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#200$26#3000#4000#100#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#1800+$22#1800$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#1800!$24#188,8+$22#1800'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs8.

Module LibSegNs_mp_baGs9.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$30$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#3000!$24#188,8+$22#3000'$22#1000#7??????00000&$22#10!$24#8,1#1"%pstring).
Definition ss0 : sym_state := SS 288400 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##453=0+$2-80$3$4$5$6$7#400$26#6000#8000#200#555555555555555^#:#::::::::::::::;#::::::::::::::;$10$11$25$30#3000+$22#3000$16$17$18$19$1:$1;$1<$1=$1>$1?,,23!$2-80,8$24!$2-78,8#46720!$2-48,8+$24#178'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22#3000!$24#188,8+$22#3000'$22#1000#7??????00000&$22#10!$24#8,1#1,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288400 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288400 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baGs9.

Module LibSegNs_mp_baJ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [235624].
Definition STOPS1 : list Z := [235624] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$30$14$35$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$25#,8#;?:88"%pstring).
Definition ss0 : sym_state := SS 288656 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 36), (384), ELit 8)].
Definition F0L : list SR.region := [((EVar 36), (384), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#39868#39868#5=#39868,20##467;4+$2-70$3$4$5$6$7$24$26$25$30#$24$26#39868$10$11$25$30$14$35$16$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$24#180,8$35'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$25#,8#;?:88,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 235624 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288656 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288656 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baJ.

Module LibSegNs_mp_baR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [288744].
Definition STOPS1 : list Z := [288744] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#10,1#"%pstring).
Definition ss0 : sym_state := SS 288692 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#467>8#467>8#5=#467>8,20#$28$2$3$4$5$6$7$29$2:#1$;$<$=$>$?$10$11$2;$2<$2=$2>$2?$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$24#8,1#1'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#10,1#,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288692 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baR.

Module LibSegNs_mp_baT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7$36$26$34$;$<$=$>$?$10$11$25$30$23$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22$23!$24#188,8+$22$23'$22#1000#7??????00000&$22#10'$23#18#6000'$34#1000#7??????00000&$34#10($34#@#2$23)$2-80#80$34#@#2$23)$24##190$34#@#2$23)$26##10$34#@#2$23)$25##60$34#@#2$23!$2-78,8#46720!$2-80,8$24'$36#2#800"%pstring).
Definition ss0 : sym_state := SS 283600 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EAlu Instr.ALU_ADD (EVar 52) (EVar 35)), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EAlu Instr.ALU_ADD (EVar 52) (EVar 35)), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##46764+$2-70$3$4$5$6$7$24$26$34$22$23$22#2$?$10$11$25$30$34++$23$34#18+$34@#18$36$17$18$19$1:$1;$1<$1=$1>$1?,,2<!+$23$34#10,8#!+$23$34#8,8$30!+$23$34#,4#2'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22$23!$24#188,8+$22$23'$22#1000#7??????00000&$22#10'$23#18#6000'$34#1000#7??????00000&$34#10($34#@#2$23)$2-80#80$34#@#2$23)$24##190$34#@#2$23)$26##10$34#@#2$23)$25##60$34#@#2$23!$2-78,8#46720!$2-80,8$24'$36#2#800,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 760184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 283600 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 283600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baT.

Module LibSegNs_mp_baU.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$30$34+$34+$23#18+$34@#2$23$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$24#178,8$22!$24#180,8+$22$23!$24#188,8+$22$23'$22#1000#7??????00000&$22#10'$23#18#6000'$34#1000#7??????00000&$34#10($34#@#2$23)$2-80#80$34#@#2$23)$24##190$34#@#2$23)$26##10$34#@#2$23)$25##60$34#@#2$23"%pstring).
Definition ss0 : sym_state := SS 288612 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-112), ELit 112); ((EVar 36), (376), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-112), 112); ((EVar 36), (376), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##46790+$2-70$3$4$5$6$7$24$26$22$23$22$=$>$?$10$11$25$30$34+$34+$23#18+$34@#2$23$17$18$19$1:$1;$1<$1=$1>$1?,,2;!$2-50,8+$22$23!$2-58,8$22!$2-60,8$22!$2-68,8$22!$24#188,8+$34@#2$23!$24#180,8+$34+$23#18!$24#178,8$34'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?'$22#1000#7??????00000&$22#10'$23#18#6000'$34#1000#7??????00000&$34#10($34#@#2$23)$2-80#80$34#@#2$23)$24##190$34#@#2$23)$26##10$34#@#2$23)$25##60$34#@#2$23,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288612 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288612 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baU.

Module LibSegNs_mp_baZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_394458.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_394458.IT.
Definition ENDS : list Z := [288744].
Definition STOPS1 : list Z := [288744] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7$24$26$:$;$<$=$>$?$10$11$25$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?"%pstring).
Definition ss0 : sym_state := SS 288760 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#467>8#467>8#5=#467>8,20#$28$2$3$4$5$6$7$29$2:#$;$<$=$>$?$10$11$2;$2<$2=$2>$2?$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$24#8,1#'$2#7???7?800080#800000000000&$2#10($2-80#80'$24#7???7?800080#7????????>70&$24#8)$2-80#80$24##190'$26#7???7?800080#7??????????0&$26#8)$2-80#80$26##10'$25#7???7?800080#7?????????:0&$25#8)$2-80#80$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#8($24#178#18!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 288744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_394458.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288760 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_394458.IT BndT_Ns_000.SegItab_Ns_394458.IT_sound BF NX0 BR XSTEP F0 PSS plan 288760 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_mp_baZ.

End BndP_Ns_049.
Module BndP_Ns_046.
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
Ltac2 kr_t_BndP_Ns_046 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_28e5332ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnE3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnHz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnIz3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnJs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046=LibSegNs_hnMs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0159;BndP_Ns_046<LibSegNs_hnN3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_hnE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [283744].
Definition STOPS1 : list Z := [283744] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 233840 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-912), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-912), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#45460#45460#5=#45460,20##3917<+$2-3:0$3$4$5$6$7$8$9+$2-380$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4!$2-390,8$:'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 283744 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233840 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233840 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnE.

Module LibSegNs_hnF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [284064].
Definition STOPS1 : list Z := [284064] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KWord (SA (EVar 2) (-400)) 8 (EVar 40)].
Definition ss0 : sym_state := SS 233852 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#455:0#455:0#5=#455:0,20##3918<+$2-3:0$3$4$5$6$7$8$9+$2-380$28+$2-398$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-190,8$28,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 284064 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233852 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233852 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnF.

Module LibSegNs_hnG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [234796].
Definition STOPS1 : list Z := [234796] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 233868 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3952<#3952<#5=#3952<,20##39194+$2-3:0$3$4$5$6$7$8$9+$2-380$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234796 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233868 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233868 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnG.

Module LibSegNs_hnHl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KWord (SA (EVar 2) (-368)) 8 (EVar 41);
   KWord (SA (EVar 2) (-352)) 8 (EVar 42);
   KRange (EVar 41) 4096 140737488355328;
   KAlign (EVar 41) 2].
Definition ss0 : sym_state := SS 233876 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-360), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-360), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##391:<+$2-3:0$3$4$5$6$7$8$9$29+@-1$29$2:$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8!$2-168,8$29'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-170,8$29!$2-160,8$2:'$29#1000#800000000000&$29#2,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233876 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnHl.

Module LibSegNs_hnHz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [233900].
Definition STOPS1 : list Z := [233900] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KWord (SA (EVar 2) (-368)) 8 (ELit 0)].
Definition ss0 : sym_state := SS 233876 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#391:<#391:<#5=#391:<,20#$1+$2-3:0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-170,8#,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 233900 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233876 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnHz.

Module LibSegNs_hnIl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KWord (SA (EVar 2) (-336)) 8 (EVar 41);
   KWord (SA (EVar 2) (-320)) 8 (EVar 42);
   KRange (EVar 41) 4096 140737488355328;
   KAlign (EVar 41) 2].
Definition ss0 : sym_state := SS 233900 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-328), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-328), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##391<4+$2-3:0$3$4$5$6$7$8$9$29+@-1$29$2:$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8!$2-148,8$29'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-150,8$29!$2-140,8$2:'$29#1000#800000000000&$29#2,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnIl.

Module LibSegNs_hnIz.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [233924].
Definition STOPS1 : list Z := [233924] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KWord (SA (EVar 2) (-336)) 8 (ELit 0)].
Definition ss0 : sym_state := SS 233900 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#391<4#391<4#5=#391<4,20#$1+$2-3:0$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,4'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-150,8#,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 233924 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233900 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233900 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnIz.

Module LibSegNs_hnJl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0%#10000#<6<<0!$2->8,1$23'$23##??'&9$23#1#1#1!$2->8,8$24!$2-=8,8$25"%pstring).
Definition ss0 : sym_state := SS 233924 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-312), ELit 8); ((EVar 2), (-296), ELit 8); ((EVar 2), (-192), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-312), 8); ((EVar 2), (-296), 8); ((EVar 2), (-192), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##39214+$2-3:0$3$4$5$6$7#<36<0$9$25@#2&6$24#1#<51>4$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,<!$2-128,8#<3598!$2-<0,8#<36;0!$2-138,8#<3688'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0%#10000#<6<<0!$2->8,1$23'$23##??'&9$23#1#1#1!$2->8,8$24!$2-=8,8$25,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233924 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnJl.

Module LibSegNs_hnJs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [590228].
Definition STOPS1 : list Z := [590228] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KImg 65536 814272;
   KWord (SA (EVar 2) (-232)) 1 (EVar 35);
   KRange (EVar 35) 0 255;
   KRange (EAlu Instr.ALU_AND (EVar 35) (ELit 1)) 0 0].
Definition ss0 : sym_state := SS 233924 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-312), ELit 8); ((EVar 2), (-296), ELit 8); ((EVar 2), (-192), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-312), 8); ((EVar 2), (-296), 8); ((EVar 2), (-192), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#90194#90194#5=#90194,20##3922<+$2-3:0$3$4$5$6$7#<36<0$9+$2-120##<51>4$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:!$2-128,8#<3518!$2-<0,8#<36;0!$2-138,8#<3688'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0%#10000#<6<<0!$2->8,1$23'$23##??'&9$23#1##,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 590228 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 233924 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 233924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnJs.

Module LibSegNs_hnK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [590228].
Definition STOPS1 : list Z := [590228] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KImg 65536 814272].
Definition ss0 : sym_state := SS 234004 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-296), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-296), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#90194#90194#5=#90194,20##3922<+$2-3:0$3$4$5$6$7$8$9+$2-120$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5!$2-128,8#<3518'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0%#10000#<6<<0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 590228 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234004 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 234004 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnK.

Module LibSegNs_hnL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [440752].
Definition STOPS1 : list Z := [440752] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928)].
Definition ss0 : sym_state := SS 234028 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6;9;0#6;9;0#5=#6;9;0,20##39240+$2-3:0$3$4$5$6$7$8$9+$2-<0+$8#8$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 440752 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234028 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 234028 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnL.

Module LibSegNs_hnMl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-28,1$23'$23##??'&9$23#1#1#1!$2-28,8$24!$2-18,8$25"%pstring).
Definition ss0 : sym_state := SS 234048 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##3925<+$2-3:0$3$4$5$6$7$8$9$25@#2&6$24#1$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-28,1$23'$23##??'&9$23#1#1#1!$2-28,8$24!$2-18,8$25,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234048 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 234048 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnMl.

Module LibSegNs_hnMs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [234092].
Definition STOPS1 : list Z := [234092] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-28,1$23'$23##??'&9$23#1##!$2-8,8$26!$2-10,8$27"%pstring).
Definition ss0 : sym_state := SS 234048 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3926<#3926<#5=#3926<,20#$26$2$3$4$5$6$7$27$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,8'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-28,1$23'$23##??'&9$23#1##!$2-8,8$26!$2-10,8$27,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234048 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 234048 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnMs.

Module LibSegNs_hnN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_28e533.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_28e533.IT.
Definition ENDS : list Z := [234092].
Definition STOPS1 : list Z := [234092] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-3:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484000 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-928)) (ELit 928);
   KWord (SA (EVar 2) (-8)) 8 (EVar 38);
   KWord (SA (EVar 2) (-16)) 8 (EVar 39)].
Definition ss0 : sym_state := SS 234076 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#3926<#3926<#5=#3926<,20#$26$2$3$4$5$6$7$27$9#$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5'$2#7???7?8003:0#800000000000&$2#10($2-3:0#3:0!$2-8,8$26!$2-10,8$27,30!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 234092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_28e533.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 234076 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_28e533.IT BndT_Ns_000.SegItab_Ns_28e533.IT_sound BF NX0 BR XSTEP F0 PSS plan 234076 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_hnN.

End BndP_Ns_046.
