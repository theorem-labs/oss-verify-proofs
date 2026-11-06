(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Ns_069.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_069 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_158e512ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skP3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_ccfb752ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_skP03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skQ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069<LibSegNs_skR3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_05133d2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0d3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0e3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srA0f3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAge3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srAlt3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBeq3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srBne3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069=LibSegNs_srC03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srCge3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_069>LibSegNs_srClt3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_skP.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$21$25$;$<$=$>$?$10$11$23$23$24$26$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$24#7???7?800000#7???????????!$24#,1$28'$28##??)$24##1$2-40#40)$24##1$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#1000#800000000000&$21#10'$23#1#3???0000'$26#2#3???0000'$25#1000#800000000000&$25#10(+$25$23##1)+$25$23##1$:##18)+$25$23##1$2-40#40)+$25$23##1$24##1"%pstring).
Definition ss0 : sym_state := SS 269704 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EVar 37) (EVar 35)), (0), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EVar 37) (EVar 35)), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##41=;8+$2-40$3$4$5$6$7$:$21$25$21$23$=$>$?$10$11$23$23++$23$25#1+$25$26$25$17$18$19$1:$1;$1<$1=$1>$1?,,1?!+$23$25#,1$28'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$24#7???7?800000#7???????????!$24#,1$28'$28##??)$24##1$2-40#40)$24##1$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#1000#800000000000&$21#10'$23#1#3???0000'$26#2#3???0000'$25#1000#800000000000&$25#10(+$25$23##1)+$25$23##1$:##18)+$25$23##1$2-40#40)+$25$23##1$24##1,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269704 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skP.

Module LibSegNs_skP0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ccfb75.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ccfb75.IT.
Definition ENDS : list Z := [269820].
Definition STOPS1 : list Z := [269820] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:#$25$;$<$=$>$?$10$11##$24#1$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$24#7???7?800000#7???????????!$24#,1$28'$28##??)$24##1$2-40#40)$24##1$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$25#1000#800000000000&$25#10($25##1)$25##1$:##18)$25##1$2-40#40)$25##1$24##1"%pstring).
Definition ss0 : sym_state := SS 269704 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (0), ELit 24); ((EVar 37), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 10), (0), 24); ((EVar 37), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=?<#41=?<#5=#41=?<,20#$2<$2$3$4$5$6$7$2=$2>$25##$25##$10$11$2?$30$31$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$:#8,8+$25#1!$:#10,8+$25#1!$:#,8$25!$25#,1$28'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$24#7???7?800000#7???????????!$24#,1$28'$28##??)$24##1$2-40#40)$24##1$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$25#1000#800000000000&$25#10($25##1)$25##1$:##18)$25##1$2-40#40)$25##1$24##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269820 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ccfb75.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269704 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ccfb75.IT BndT_Ns_002.SegItab_Ns_ccfb75.IT_sound BF NX0 BR XSTEP F0 PSS plan 269704 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skP0.

Module LibSegNs_skQ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$21$25$;$<$=$>$?$10$11$23$23++$25$23#1+$25$26$25$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#1000#800000000000'$23#1#3???0000'$26#2#3???0000'$25#1000#800000000000"%pstring).
Definition ss0 : sym_state := SS 269752 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##41==4+$2-40$3$4$5$6$7$:$21$21$23$<$=$>$?$10$11$23$23++$25$23#1+$25$26$25$17$18$19$1:$1;$1<$1=$1>$1?,,16!$:#10,8+$25$26!$:#8,8++$25$23#1!$:#,8$25'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#1000#800000000000'$23#1#3???0000'$26#2#3???0000'$25#1000#800000000000,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269752 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269752 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skQ.

Module LibSegNs_skR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [269820].
Definition STOPS1 : list Z := [269820] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$9$37$;$<$=$>$?$10$11$12$13$29$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33"%pstring).
Definition ss0 : sym_state := SS 269780 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 10), (8), ELit 8)].
Definition F0L : list SR.region := [((EVar 10), (8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=?<#41=?<#5=#41=?<,20#$2<$2$3$4$5$6$7$2=$2>$37$;$<$=$>$?$10$11$2?$30$31$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,10!$:#8,8$29'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269820 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269780 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269780 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skR.

Module LibSegNs_srA0d.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [440916].
Definition STOPS1 : list Z := [440916] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; ELit 16384; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10"%pstring).
Definition ss0 : sym_state := SS 287388 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#6;:54#6;:54#5=#6;:54,20##463;4+$2-30$3$4$5$6$7$24#+$2=#10$25#4000#6;:54$>$?$10$11$25#4000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10,30!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srA0d.

Module LibSegNs_srA0e.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [287768].
Definition STOPS1 : list Z := [287768] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; ELit 16384; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#2!$2=#9<,4#!$2=#:0,8+$2=#10"%pstring).
Definition ss0 : sym_state := SS 287388 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46418#46418#5=#46418,20#$1$2$3$4$5$6$7$8$9##78#4000$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#120,8#!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23,$24#100#8($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#2!$2=#9<,4#!$2=#:0,8+$2=#10,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 287768 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srA0e.

Module LibSegNs_srA0f.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [291092].
Definition STOPS1 : list Z := [291092] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 38; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8($24#100#28'$26#1#3???"%pstring).
Definition ss0 : sym_state := SS 287388 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47114#47114#5=#47114,20##46334+$2-30$3$4$5$6$7$24#$24$22#4000$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$24#118,8$22!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#120,8#,$24#100#8($24#100#28'$26#1#3???,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srA0f.

Module LibSegNs_srAge.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 38; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483120 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KRange (EVar 33) 1 16384;
   KRange (EVar 38) 1 16384;
   KRange (APC.esub (EVar 38) (EVar 33)) 0 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 287388 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##462>4+$2-30$3$4$5$6$7$24$21$25$23$21$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8$21,$24#100#8($24#100#28'$21#1#4000'$26#1#4000'+@-1$21$26##3???'$23#1000#7???????<000,30!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srAge.

Module LibSegNs_srAlt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 36; EVar 37; EVar 38; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483120 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KRange (EVar 33) 2 16384;
   KRange (EVar 38) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 38)) 1 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 287388 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##462>4+$2-30$3$4$5$6$7$24$26$25$23$26$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8$21,$24#100#8($24#100#28'$21#2#4000'$26#1#3???'+$21@-1$26#1#3???'$23#1000#7???????<000,30!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287388 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287388 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srAlt.

Module LibSegNs_srBeq.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [287768].
Definition STOPS1 : list Z := [287768] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24$27$:$;$<$=$>$?$10$11$25$27$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483120 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KWord (SA (EVar 2) (-8)) 8 (EVar 40);
   KWord (SA (EVar 2) (-16)) 8 (EVar 41);
   KWord (SA (EVar 2) (-24)) 8 (EVar 42);
   KWord (SA (EVar 2) (-32)) 8 (EVar 43);
   KWord (SA (EVar 2) (-40)) 8 (EVar 44);
   KRange (EVar 33) 1 16384;
   KRange (EVar 39) 1 16384;
   KRange (APC.esub (EVar 33) (EVar 39)) 0 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 287460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46418#46418#5=#46418,20#$28$2$3$4$5$6$7$29$2:$27+$21@-1$27+$27$30$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$24#120,8+$21@-1$27!$24#118,8+$23$27!$24#100,8+$27$30'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21#1#4000'$27#1#4000'+$21@-1$27##3???'$23#1000#7???????<000,31!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 287768 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287460 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srBeq.

Module LibSegNs_srBne.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [291092].
Definition STOPS1 : list Z := [291092] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24$27$:$;$<$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483120 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 35);
   KWord (SA (EVar 36) (288)) 8 (EVar 39);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KWord (SA (EVar 2) (-8)) 8 (EVar 40);
   KWord (SA (EVar 2) (-16)) 8 (EVar 41);
   KWord (SA (EVar 2) (-24)) 8 (EVar 42);
   KWord (SA (EVar 2) (-32)) 8 (EVar 43);
   KWord (SA (EVar 2) (-40)) 8 (EVar 44);
   KRange (EVar 39) 1 16383;
   KRange (EVar 38) 2 16384;
   KRange (APC.esub (EVar 38) (EVar 39)) 1 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 287460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47114#47114#5=#47114,20##46334+$2-30$3$4$5$6$7$24$27$24$22#4000$=$>$?$10$11$25+$26@-1$27$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$24#118,8$22!$24#120,8#!$24#100,8+$27$30'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$27#1#3???'$26#2#4000'+$26@-1$27#1#3???'$23#1000#7???????<000,31!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291092 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287460 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srBne.

Module LibSegNs_srC0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [287768].
Definition STOPS1 : list Z := [287768] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24$27#$;$<$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22!$24#120,8#,$24#100#8($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 287540 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46418#46418#5=#46418,20#$28$2$3$4$5$6$7$29$2:$27$;$<$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$24#120,8#'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22,$24#100#8($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 287768 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srC0.

Module LibSegNs_srCge.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24$27$21$;$<$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483120 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 34);
   KWord (SA (EVar 36) (288)) 8 (ELit 0);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KWord (SA (EVar 2) (-8)) 8 (EVar 40);
   KWord (SA (EVar 2) (-16)) 8 (EVar 41);
   KWord (SA (EVar 2) (-24)) 8 (EVar 42);
   KWord (SA (EVar 2) (-32)) 8 (EVar 43);
   KWord (SA (EVar 2) (-40)) 8 (EVar 44);
   KRange (EVar 33) 1 16383;
   KRange (EVar 38) 1 16383;
   KRange (APC.esub (EVar 38) (EVar 33)) 0 16383;
   KRange (EVar 39) 0 16383;
   KRange (EVar 37) 0 140737488355328].
Definition ss0 : sym_state := SS 287540 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##46354+$2-30$3$4$5$6$7$24$27+$25$27$22$21$=$>$?$10$11$25$21$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#120,8$21'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22,$24#100#8($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21#1#3???'$26#1#3???'+@-1$21$26##3???'$27##3???'$25##800000000000,30!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srCge.

Module LibSegNs_srClt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_05133d.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_05133d.IT.
Definition ENDS : list Z := [760184].
Definition STOPS1 : list Z := [760184] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24$27$21$;$<$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483120 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-48)) (ELit 48);
   KRange (EVar 36) 140735332483120 140737488355032;
   KAlign (EVar 36) 8;
   KDisj (SA (EVar 2) (-48)) (ELit 48) (SA (EVar 36) 0) (ELit 296);
   KWord (SA (EVar 36) (264)) 8 (EVar 34);
   KWord (SA (EVar 36) (272)) 8 (ELit 16384);
   KWord (SA (EVar 36) (280)) 8 (EVar 34);
   KWord (SA (EVar 36) (288)) 8 (ELit 0);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KWord (SA (EVar 2) (-8)) 8 (EVar 40);
   KWord (SA (EVar 2) (-16)) 8 (EVar 41);
   KWord (SA (EVar 2) (-24)) 8 (EVar 42);
   KWord (SA (EVar 2) (-32)) 8 (EVar 43);
   KWord (SA (EVar 2) (-40)) 8 (EVar 44);
   KRange (EVar 33) 2 16384;
   KRange (EVar 38) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 38)) 1 16383;
   KRange (EVar 39) 0 16383;
   KRange (EVar 37) 0 140737488355328].
Definition ss0 : sym_state := SS 287540 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9978#;9978#5=#;9978,20##46354+$2-30$3$4$5$6$7$24$27+$25$27$22$26$=$>$?$10$11$25$26$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#120,8$21'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$22,$24#100#8($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21#2#4000'$26#1#3???'+$21@-1$26#1#3???'$27##3???'$25##800000000000,30!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srClt.

End BndP_Ns_069.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_001.
Module BndP_Ns_068.
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
Ltac2 kr_t_BndP_Ns_068 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_18bef92ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2222BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2223NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2222BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2225XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2222F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2223PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2224planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2225regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2223kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2232BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2233NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2232BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2235XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2232F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2233PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2234planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2235regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068?LibSegNs_riT2233kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_riZ3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_b208c82ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_rsS3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_50cfc82ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBe3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBg3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvBs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_rvN13kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_158e512ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068<LibSegNs_skF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_068=LibSegNs_skG23kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_riT222.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [287860].
Definition STOPS1 : list Z := [287860] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26#1$;$<$=$>$?$10$11$25+$24#18$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-39,1#=>"%pstring).
Definition ss0 : sym_state := SS 284676 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46474#46474#5=#46474,20##4595<+$2-90$3$4$5$6$7$24$26$24$25#=>$26$>$?$10$11$25+$24#18$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-39,1#=>,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 287860 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284676 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 284676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_riT222.

Module LibSegNs_riT223.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_18bef9.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_18bef9.IT.
Definition ENDS : list Z := [287860].
Definition STOPS1 : list Z := [287860] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-90$3$4$5$6$7$24$26#1$;$<$=$>$?$10$11$25+$24#18$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-39,1#=?"%pstring).
Definition ss0 : sym_state := SS 284676 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46474#46474#5=#46474,20##4595<+$2-90$3$4$5$6$7$24$26$24$25#=?$26$>$?$10$11$25+$24#18$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-39,1#=?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 287860 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 284676 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 284676 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_riT223.

Module LibSegNs_riZ.
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
Definition ss0 : sym_state := SS 286876 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#460<0#460<0#5=#460<0,20#$28$2$3$4$5$6$7$29$2:$:$;$<$=$>$?$10$11$2;$2<$2=$2>$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$24#8,1#'$2#7???7?800090#800000000000&$2#10($2-90#90'$24#7???7?800090#7????????>70&$24#8)$2-90#90$24##190'$26#7???7?800090#7??????????0&$26#8)$2-90#90$26##10'$25#7???7?800090#7?????????:0&$25#8)$2-90#90$25##60%#10000#<6<<0)$24##190$25##60)$26##10$25##60)$24##190$26##10($24#8#1!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_18bef9.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 286876 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_18bef9.IT BndT_Ns_000.SegItab_Ns_18bef9.IT_sound BF NX0 BR XSTEP F0 PSS plan 286876 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_riZ.

Module LibSegNs_rsL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_b208c8.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_b208c8.IT.
Definition ENDS : list Z := [284060].
Definition STOPS1 : list Z := [284060] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800050#800000000000&$2#10($2-50#50($:##190'$:#1000#800000000000&$:#8)$2-50#50$:##190!$:#148,1$21'$21##??'&9$21#1#1#1!$:#158,8$25'$25#1000#800000000000($25##1)$2-50#50$25##1)$25##1$:##190)$25##1$22##18!$:#160,8$24!$:#178,8$22'$22#1000#800000000000&$22#10'$23#18#<000!$:#188,8+$22$23($22##18)$2-50#50$22##18)$22##18$:##190"%pstring).
Definition ss0 : sym_state := SS 283744 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8); ((EVar 10), (336), ELit 8); ((EVar 10), (360), ELit 8); ((EVar 10), (384), ELit 8); ((EVar 34), (0), ELit 24); ((EVar 37), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 10), (8), 8); ((EVar 10), (336), 8); ((EVar 10), (360), 8); ((EVar 10), (384), 8); ((EVar 34), (0), 24); ((EVar 37), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4559<#4559<#5=#4559<,20#$1$2$3$4$5$6$7$8$9$22+$22$23$24$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,27!$:#<,4#!$:#180,8+$22#18!$22#10,8#!$22#8,8#!$22#,4#!$:#168,8$24!$:#150,8#!$25#,1#!$:#8,2#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50($:##190'$:#1000#800000000000&$:#8)$2-50#50$:##190!$:#148,1$21'$21##??'&9$21#1#1#1!$:#158,8$25'$25#1000#800000000000($25##1)$2-50#50$25##1)$25##1$:##190)$25##1$22##18!$:#160,8$24!$:#178,8$22'$22#1000#800000000000&$22#10'$23#18#<000!$:#188,8+$22$23($22##18)$2-50#50$22##18)$22##18$:##190,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_b208c8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 283744 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_b208c8.IT BndT_Ns_001.SegItab_Ns_b208c8.IT_sound BF NX0 BR XSTEP F0 PSS plan 283744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rsL.

Module LibSegNs_rsS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_b208c8.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_b208c8.IT.
Definition ENDS : list Z := [284060].
Definition STOPS1 : list Z := [284060] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800050#800000000000&$2#10($2-50#50($:##190'$:#1000#800000000000&$:#8)$2-50#50$:##190!$:#148,1$21'$21##??'&9$21#1##!$:#160,8$24!$:#178,8$22'$22#1000#800000000000&$22#10'$23#18#<000!$:#188,8+$22$23($22##18)$2-50#50$22##18)$22##18$:##190"%pstring).
Definition ss0 : sym_state := SS 283744 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 10), (8), ELit 8); ((EVar 10), (328), ELit 2); ((EVar 10), (360), ELit 8); ((EVar 10), (384), ELit 8); ((EVar 34), (0), ELit 24)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 10), (8), 8); ((EVar 10), (328), 2); ((EVar 10), (360), 8); ((EVar 10), (384), 8); ((EVar 34), (0), 24)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4559<#4559<#5=#4559<,20#$1$2$3$4$5$6$7$8$9$22+$22$23$24$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$:#<,4#!$:#180,8+$22#18!$22#10,8#!$22#8,8#!$22#,4#!$:#168,8$24!$:#148,2#!$:#8,2#1!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800050#800000000000&$2#10($2-50#50($:##190'$:#1000#800000000000&$:#8)$2-50#50$:##190'$21##??'&9$21#1##!$:#160,8$24!$:#178,8$22'$22#1000#800000000000&$22#10'$23#18#<000!$:#188,8+$22$23($22##18)$2-50#50$22##18)$22##18$:##190,30!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 284060 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_b208c8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 283744 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_b208c8.IT BndT_Ns_001.SegItab_Ns_b208c8.IT_sound BF NX0 BR XSTEP F0 PSS plan 283744 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rsS.

Module LibSegNs_rvBe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_50cfc8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_50cfc8.IT.
Definition ENDS : list Z := [291676].
Definition STOPS1 : list Z := [291676] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 35); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$21#1000#7?????????>8&$21#8($21##18!$21#,8$22!$21#8,8+$22$23!$21#10,8+$22+$23$24'$22#1000#800000000000&$22#10'$23##8008000'$24##8008000"%pstring).
Definition ss0 : sym_state := SS 291640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4735<#4735<#5=#4735<,20#$1$2$3$4$5$6$7$8$9$21$23$22$23$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$21#1000#7?????????>8&$21#8($21##18!$21#,8$22!$21#8,8+$22$23!$21#10,8+$22+$23$24'$22#1000#800000000000&$22#10'$23##8008000'$24##8008000,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291676 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_50cfc8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_50cfc8.IT BndT_Ns_000.SegItab_Ns_50cfc8.IT_sound BF NX0 BR XSTEP F0 PSS plan 291640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rvBe.

Module LibSegNs_rvBg.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_50cfc8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_50cfc8.IT.
Definition ENDS : list Z := [291680].
Definition STOPS1 : list Z := [291680] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$23$25$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$21#1000#7?????????>8&$21#8($21##18!$21#,8$22!$21#8,8+$22$23!$21#10,8+$22+$23$24'$22#1000#800000000000&$22#10'$23##8008000'$25#1#8008000'$24##8008000"%pstring).
Definition ss0 : sym_state := SS 291640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47360#47360#5=#47360,20#$1$2$3$4$5$6$7$8$9$21$25$22$23$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'$21#1000#7?????????>8&$21#8($21##18!$21#,8$22!$21#8,8+$22$23!$21#10,8+$22+$23$24'$22#1000#800000000000&$22#10'$23##8008000'$25#1#8008000'$24##8008000,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291680 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_50cfc8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_50cfc8.IT BndT_Ns_000.SegItab_Ns_50cfc8.IT_sound BF NX0 BR XSTEP F0 PSS plan 291640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rvBg.

Module LibSegNs_rvBs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_50cfc8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_50cfc8.IT.
Definition ENDS : list Z := [291676].
Definition STOPS1 : list Z := [291676] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 37); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$21#1000#7?????????>8&$21#8($21##18!$21#,8$22!$21#8,8+$22+$25$27!$21#10,8+$22++$25$27$24'$22#1000#800000000000&$22#10'$25##8008000'$27#1#8008000'$24##8008000"%pstring).
Definition ss0 : sym_state := SS 291640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4735<#4735<#5=#4735<,20#$1$2$3$4$5$6$7$8$9$21+$22$25$22+$25$27$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,;!$21#8,8+$22$25'$21#1000#7?????????>8&$21#8($21##18!$21#,8$22!$21#10,8+$22++$25$27$24'$22#1000#800000000000&$22#10'$25##8008000'$27#1#8008000'$24##8008000,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291676 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_50cfc8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_50cfc8.IT BndT_Ns_000.SegItab_Ns_50cfc8.IT_sound BF NX0 BR XSTEP F0 PSS plan 291640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rvBs.

Module LibSegNs_rvN0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_50cfc8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_50cfc8.IT.
Definition ENDS : list Z := [291676].
Definition STOPS1 : list Z := [291676] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 4096 140737488355304;
   KAlign (EVar 33) 8;
   KWr (SA (EVar 33) 0) (ELit 24);
   KWord (SA (EVar 33) (0)) 8 (ELit 0);
   KWord (SA (EVar 33) (8)) 8 (ELit 0);
   KWord (SA (EVar 33) (16)) 8 (ELit 0)].
Definition ss0 : sym_state := SS 291640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4735<#4735<#5=#4735<,20#$1$2$3$4$5$6$7$8$9$21###$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'$21#1000#7?????????>8&$21#8($21##18!$21#,8#!$21#8,8#!$21#10,8#,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291676 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_50cfc8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_50cfc8.IT BndT_Ns_000.SegItab_Ns_50cfc8.IT_sound BF NX0 BR XSTEP F0 PSS plan 291640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rvN0.

Module LibSegNs_rvN1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_50cfc8.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_50cfc8.IT.
Definition ENDS : list Z := [291680].
Definition STOPS1 : list Z := [291680] ++ ENDS.
Definition NX0 : nat := 52.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 37); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 33) 4096 140737488355304;
   KAlign (EVar 33) 8;
   KWr (SA (EVar 33) 0) (ELit 24);
   KWord (SA (EVar 33) (0)) 8 (ELit 0);
   KWord (SA (EVar 33) (8)) 8 (ELit 0);
   KWord (SA (EVar 33) (16)) 8 (ELit 0);
   KRange (EVar 37) 1 134250496].
Definition ss0 : sym_state := SS 291640 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47360#47360#5=#47360,20#$1$2$3$4$5$6$7$8$9$21$25##$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,7'$21#1000#7?????????>8&$21#8($21##18!$21#,8#!$21#8,8#!$21#10,8#'$25#1#8008000,34!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291680 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_50cfc8.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291640 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_50cfc8.IT BndT_Ns_000.SegItab_Ns_50cfc8.IT_sound BF NX0 BR XSTEP F0 PSS plan 291640 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_rvN1.

Module LibSegNs_skF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [269820].
Definition STOPS1 : list Z := [269820] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8$21!$:#8,8+$21$22!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$22##800000000000'$23#1#800000000000'+$23@-1$22#1#800000000000(+$21$22##1)+$21$22##1$:##18)+$21$22##1$2-40#40)+$21$22##1$;##1"%pstring).
Definition ss0 : sym_state := SS 269572 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-64), ELit 64); ((EVar 10), (8), ELit 8); ((EAlu Instr.ALU_ADD (EVar 33) (EVar 34)), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 2), (-64), 64); ((EVar 10), (8), 8); ((EAlu Instr.ALU_ADD (EVar 33) (EVar 34)), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41=?<#41=?<#5=#41=?<,20#$1$2$3$4$5$6$7$8$9$28$;+$21$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$:#8,8++$21$22#1!+$21$22#,1$28!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8$21!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$22##800000000000'$23#1#800000000000'+$23@-1$22#1#800000000000(+$21$22##1)+$21$22##1$:##18)+$21$22##1$2-40#40)+$21$22##1$;##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269820 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skF.

Module LibSegNs_skG0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8#!$:#8,8#!$:#10,8#"%pstring).
Definition ss0 : sym_state := SS 269572 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##41=88+$2-40$3$4$5$6$7$:##1^#3#???????????????#$=$>$?$10$11##$;#1$16$17$18$19$1:$1;$1<$1=$1>$1?,,17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8#!$:#8,8#!$:#10,8#,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skG0.

Module LibSegNs_skG1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8$21!$:#8,8+$21$23!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$23#2#1???8000"%pstring).
Definition ss0 : sym_state := SS 269572 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##41=88+$2-40$3$4$5$6$7$:$21@#2$23^#3#???????????????+$21$23$=$>$?$10$11$23$23$;@#2$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8$21!$:#8,8+$21$23!$:#10,8+$21$23'$21#1000#800000000000&$21#10'$23#2#1???8000,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skG1.

Module LibSegNs_skG2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_158e51.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_158e51.IT.
Definition ENDS : list Z := [780464].
Definition STOPS1 : list Z := [780464] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8$21!$:#8,8+$21#1!$:#10,8+$21#1'$21#1000#800000000000&$21#10"%pstring).
Definition ss0 : sym_state := SS 269572 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;>8;0#;>8;0#5=#;>8;0,20##41=88+$2-40$3$4$5$6$7$:$21#2^#3#???????????????+$21#1$=$>$?$10$11#1#1$;#2$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$:#7???7?800000#7?????????>8&$:#8($:##18)$2-40#40$:##18'$;#7???7?800000#7???????????!$;#,1$28'$28##??)$;##1$2-40#40)$;##1$:##18!$:#,8$21!$:#8,8+$21#1!$:#10,8+$21#1'$21#1000#800000000000&$21#10,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_158e51.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 269572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_158e51.IT BndT_Ns_000.SegItab_Ns_158e51.IT_sound BF NX0 BR XSTEP F0 PSS plan 269572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_skG2.

End BndP_Ns_068.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_001 BndT_Ns_002.
Module BndP_Ns_083.
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
Ltac2 kr_t_BndP_Ns_083 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_001ASegItab_Ns_7efbb42ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00c3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW00s3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txW01s3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN0s3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1c3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083?LibSegNs_txWN1s3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txX3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_txZ3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_ee5b3c2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083<LibSegNs_vaE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_083=LibSegNs_vaF83kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_txW00c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#'&9$26#2##"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:##$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#'&9$26#2##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txW00c.

Module LibSegNs_txW00s.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#'&9$26#2#2#2"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:##$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#'&9$26#2#2#2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txW00s.

Module LibSegNs_txW01c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#1'&9$26#2##"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:#+&5$3<&7$3<#3?@-1&7$3<#3?$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#1'&9$26#2##,3=!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txW01c.

Module LibSegNs_txW01s.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#1'&9$26#2#2#2"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:#+&5$3<&7$3<#3?@-1&7$3<#3?$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8#!$2-70,8#1'&9$26#2#2#2,3=!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txW01s.

Module LibSegNs_txWN0c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#'&9$26#2##"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:$3<#$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#'&9$26#2##,3=!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txWN0c.

Module LibSegNs_txWN0s.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#'&9$26#2#2#2"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:@-1$3<#$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#'&9$26#2#2#2,3=!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txWN0s.

Module LibSegNs_txWN1c.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#1'&9$26#2##"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:$3<+&5$3=&7$3=#3?@-1&7$3=#3?$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#1'&9$26#2##,3>!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txWN1c.

Module LibSegNs_txWN1s.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#1'&9$26#2#2#2"%pstring).
Definition ss0 : sym_state := SS 264948 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40<10+$2-:0$3$4$5$6$7$:$2?$:@-1$3<+&5$3=&7$3=#3?@-1&7$3=#3?$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,10'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-98,1#!$2-58,1$26'$26##??'&9$26#1##!$2-78,1$2:'$2:##??'&9$2:#1##,$2-48#10,$2-68#10!$2-50,8$27'$27#1#2!$2-70,8#1'&9$26#2#2#2,3>!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264948 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264948 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txWN1s.

Module LibSegNs_txX.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?$37$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-38,1$25'$25##??'&9$25#1##!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>"%pstring).
Definition ss0 : sym_state := SS 264740 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#40:90#40:90#5=#40:90,20#$2<$2$3$4$5$6$7$2=$2>#1$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?8000:0#800000000000&$2#10($2-:0#:0!$2-38,1$25'$25##??'&9$25#1##!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 264848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264740 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264740 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txX.

Module LibSegNs_txZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_001.SegItab_Ns_7efbb4.ITR.
Definition IT : itab := BndT_Ns_001.SegItab_Ns_7efbb4.IT.
Definition ENDS : list Z := [269848].
Definition STOPS1 : list Z := [269848] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$:$2?#$38$39$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483232 140737488355328;
   KAlign (EVar 2) 16].
Definition ss0 : sym_state := SS 264860 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#41>18#41>18#5=#41>18,20##40;54+$2-:0$3$4$5$6$7$:$2?$:##$3:$>$3;$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'$2#7???7?8000:0#800000000000&$2#10,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 269848 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_001.SegItab_Ns_7efbb4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 264860 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_001.SegItab_Ns_7efbb4.IT BndT_Ns_001.SegItab_Ns_7efbb4.IT_sound BF NX0 BR XSTEP F0 PSS plan 264860 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_txZ.

Module LibSegNs_vaB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ee5b3c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ee5b3c.IT.
Definition ENDS : list Z := [289444; 289100].
Definition STOPS1 : list Z := [289444; 289100] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$25$;+$21$23#8#1-3>#?5-41#2#15==:#3$15$21$17$18$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 0 140737488355328;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 0 140737488355328].
Definition ss0 : sym_state := SS 289404 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46::4#4694<#46::4#4694<#5;#46:80,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#15==:#3$15$21$17$18$19$1:$1;#>=#9?#?0#90,,3'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46::4#4694<#46::4#4694<#5=#46::4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21$23#+$21$23#8#1-3>#?5-41#2#15==:#3$15$21$17$18$19$1:$1;#>=#9?#?0#90,,4'&4&1$21+$21$23#1#1#1'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46::4#4694<#46::4#4694<#5=#4694<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#15==:#3$15$21$17$18$19$1:$1;#>=#9?#?0#90,,4'&4&1$21+$21$23#1##'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 289444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 289100 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ee5b3c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289404 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ee5b3c.IT BndT_Ns_002.SegItab_Ns_ee5b3c.IT_sound BF NX0 BR XSTEP F0 PSS plan 289404 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vaB.

Module LibSegNs_vaE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ee5b3c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ee5b3c.IT.
Definition ENDS : list Z := [289492; 289100].
Definition STOPS1 : list Z := [289492; 289100] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 35); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483168 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-96)) (ELit 96);
   KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 0 67108863].
Definition ss0 : sym_state := SS 288972 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-88), ELit 88)].
Definition F0L : list SR.region := [((EVar 2), (-88), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46:=4#4694<#46:=4#4694<#5=#46:=4,20#$1$2$3$4$5$6$7$8$9$21$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6'&4&1$23##1#1#1'$2#7???7?800060#800000000000&$2#10($2-60#60'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#46:=4#4694<#46:=4#4694<#5=#4694<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#15908+$21$23#8#1^#?#?????????????<2#?5^#?#?????????????;?#2#15==:#3$15$16$17$18$19$1:$1;#>=#9?#?0#90,,11!$2-58,8$1:!$2-50,8$19!$2-48,8$18!$2-40,8$17!$2-38,8$16!$2-30,8$15!$2-28,8$14!$2-20,8$13!$2-18,8$12!$2-10,8$9!$2-8,8$8'&4&1$23##1##'$2#7???7?800060#800000000000&$2#10($2-60#60'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s2).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s2).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s2 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s2 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s2).
Definition ps0 : SR.post_spec := SR.PS 289492 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 289100 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ee5b3c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 288972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ee5b3c.IT BndT_Ns_002.SegItab_Ns_ee5b3c.IT_sound BF NX0 BR XSTEP F0 PSS plan 288972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vaE.

Module LibSegNs_vaF1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ee5b3c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ee5b3c.IT.
Definition ENDS : list Z := [289232].
Definition STOPS1 : list Z := [289232] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#15==:#3$15$16$17$18$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 7;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255].
Definition ss0 : sym_state := SS 289100 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#469=0#469=0#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$24$16$17$18$19$1:$1;#>=#9?#?0#90,,5'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ee5b3c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289100 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ee5b3c.IT BndT_Ns_002.SegItab_Ns_ee5b3c.IT_sound BF NX0 BR XSTEP F0 PSS plan 289100 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vaF1.

Module LibSegNs_vaF8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_ee5b3c.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_ee5b3c.IT.
Definition ENDS : list Z := [289232; 289404].
Definition STOPS1 : list Z := [289232; 289404] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#15==:#3$15$16$17$18$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??"%pstring).
Definition ss0 : sym_state := SS 289100 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46958,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$24$16$17$18$19$1:$1;#>=#9?#?0#90,,13'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$24$16$17$18$19$1:$1;#>=#9?#?0#90,,14'&3],,1$24##1#1'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46960,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$25$16$17$18$19$1:$1;#>=#9?#?0#90,,14'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#1$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$25$16$17$18$19$1:$1;#>=#9?#?0#90,,15'&3],,1$25##1#1'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46968,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$26$16$17$18$19$1:$1;#>=#9?#?0#90,,15'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#2$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$26$16$17$18$19$1:$1;#>=#9?#?0#90,,16'&3],,1$26##1#1'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition ex10 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46970,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$27$16$17$18$19$1:$1;#>=#9?#?0#90,,16'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).

Definition arms11 := Eval vm_compute in (match SGP.branch_probe IT s10 with Some e => SGP.case_arms s10 e 0 | None => None end).
Definition f11 : sym_state := match arms11 with Some (Some s, _) => s | _ => s10 end.
Definition t11 : sym_state := match arms11 with Some (_, Some s) => s | _ => s10 end.

Definition ex12 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#3$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$27$16$17$18$19$1:$1;#>=#9?#?0#90,,17'&3],,1$27##1#1'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).

Definition ex13 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46978,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$28$16$17$18$19$1:$1;#>=#9?#?0#90,,17'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s13 : sym_state := snd (snd ex13).

Definition arms14 := Eval vm_compute in (match SGP.branch_probe IT s13 with Some e => SGP.case_arms s13 e 0 | None => None end).
Definition f14 : sym_state := match arms14 with Some (Some s, _) => s | _ => s13 end.
Definition t14 : sym_state := match arms14 with Some (_, Some s) => s | _ => s13 end.

Definition ex15 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#4$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$28$16$17$18$19$1:$1;#>=#9?#?0#90,,18'&3],,1$28##1#1'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s15 : sym_state := snd (snd ex15).

Definition ex16 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46980,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$29$16$17$18$19$1:$1;#>=#9?#?0#90,,18'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).

Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#5$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$29$16$17$18$19$1:$1;#>=#9?#?0#90,,19'&3],,1$29##1#1'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition ex19 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46988,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$2:$16$17$18$19$1:$1;#>=#9?#?0#90,,19'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).

Definition arms20 := Eval vm_compute in (match SGP.branch_probe IT s19 with Some e => SGP.case_arms s19 e 0 | None => None end).
Definition f20 : sym_state := match arms20 with Some (Some s, _) => s | _ => s19 end.
Definition t20 : sym_state := match arms20 with Some (_, Some s) => s | _ => s19 end.

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#6$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$2:$16$17$18$19$1:$1;#>=#9?#?0#90,,1:'&3],,1$2:##1#1'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition ex22 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5;#46990,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$2;$16$17$18$19$1:$1;#>=#9?#?0#90,,1:'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).

Definition arms23 := Eval vm_compute in (match SGP.branch_probe IT s22 with Some e => SGP.case_arms s22 e 0 | None => None end).
Definition f23 : sym_state := match arms23 with Some (Some s, _) => s | _ => s22 end.
Definition t23 : sym_state := match arms23 with Some (_, Some s) => s | _ => s22 end.

Definition ex24 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#469=0,20#$1+$2-60$3$4#>?#>0#:0#?4#8?+$21#7$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$2;$16$17$18$19$1:$1;#>=#9?#?0#90,,1;'&3],,1$2;##1#1'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).

Definition ex25 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#469=0#46:7<#469=0#46:7<#5=#46:7<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$23+$21$23#8#1-3>#?5-41#2#15==:#3],,1$2;+$21#8$17$18$19$1:$1;#>=#9?#?0#90,,1;'&3],,1$2;###'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s25 : sym_state := snd (snd ex25).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PBranch (SGA.mkplan (fst ex12) (SGP.PEnd 3)) (SGA.mkplan (fst ex13) (SGP.PBranch (SGA.mkplan (fst ex15) (SGP.PEnd 4)) (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 5)) (SGA.mkplan (fst ex19) (SGP.PBranch (SGA.mkplan (fst ex21) (SGP.PEnd 6)) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PEnd 7)) (SGA.mkplan (fst ex25) (SGP.PEnd 8))))))))))))))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s12).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s12).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s12 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s12 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s12).
Definition ps3 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s15).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s15).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s15 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s15 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s15).
Definition ps4 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s18).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s18).
Definition ps5 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s24).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s24).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s24 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s24 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s24).
Definition ps7 : SR.post_spec := SR.PS 289232 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition regs_out8 : list expr := Eval vm_compute in (s_regs s25).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s25).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s25 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s25 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s25).
Definition ps8 : SR.post_spec := SR.PS 289404 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_ee5b3c.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 289100 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_ee5b3c.IT BndT_Ns_002.SegItab_Ns_ee5b3c.IT_sound BF NX0 BR XSTEP F0 PSS plan 289100 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_vaF8.

End BndP_Ns_083.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002.
Module BndP_Ns_074.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_074 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bebaca2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1bp3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1en3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1ep3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV1sp3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2an3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074?LibSegNs_teV2ap3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b00p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b01p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b10p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_074ALibSegNs_teV2b11n3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_teV1bp.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5;#43464,20##43460+$2-1:0$3$4$41$42$43+$2#28&4#/7$24#3;9:<:00###2$47$48$49$4:$4;#+$2-<8#+$2-78+$2-98+$2#78+$2#58$19#+$2#28$4<$4=$4>$4?,,49!$2#30,8&4#/7$24#3;9:<:00!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24#3;9:<:00!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24#3;9:<:00!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24#3;9:<:00!$2-<0,8&4#/7$24#3;9:<:00!$2-<8,1#!$2#58,8/5$24#3;9:<:00!$2#48,1#!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#38,8#!$2#40,8#!$2#68,1#!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ce2 : expr := EMd Instr.M_REMU (EVar 36) (ELit 1000000000).
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9###2$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,4:!$2#28,1#!$2#48,1#'/7$24#3;9:<:00##!$2#30,8&4#/7$24#3;9:<:00!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24#3;9:<:00!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24#3;9:<:00!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24#3;9:<:00!$2-<0,8&4#/7$24#3;9:<:00!$2-<8,1#!$2#58,8/5$24#3;9:<:00!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#68,1#!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$51$52$53$8$9##$56$57$58$59$5:$5;$12$13$14$15$16$17$18$19$1:$1;$5<$5=$5>$5?,,4:!$2#28,1#!$2#48,1#!$2#38,8/7$24#3;9:<:00!$2#40,8#'/7$24#3;9:<:00#1#3;9:<9??!$2#30,8&4#/7$24#3;9:<:00!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24#3;9:<:00!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24#3;9:<:00!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24#3;9:<:00!$2-<0,8&4#/7$24#3;9:<:00!$2-<8,1#!$2#58,8/5$24#3;9:<:00!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#68,1#!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????,60!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV1bp.

Module LibSegNs_teV1en.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#1!$2#78,8#3;9:<:00!$2#80,8#"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##2#2$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,48!$2#28,1#2!$2#48,1#2!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42634!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2#58,8#1!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8#!$2-98,8#3;9:<:00!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#68,1#2!$2#70,8#1!$2#78,8#3;9:<:00!$2#80,8#,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV1en.

Module LibSegNs_teV1ep.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#1!$2#78,8#3;9:<:00!$2#80,8#"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9###2$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,48!$2#28,1#!$2#48,1#!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#!$2-138,8#42634!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2#58,8#1!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8#!$2-98,8#3;9:<:00!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#68,1#!$2#70,8#1!$2#78,8#3;9:<:00!$2#80,8#,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV1ep.

Module LibSegNs_teV1sn.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#1#3;9:<9??"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9#$45$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,47!$2#28,1#2!$2#38,8$24!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8&9+@#4&6$31#2#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42580!$2#48,1#2!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#1#3;9:<9??,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV1sn.

Module LibSegNs_teV1sp.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#1#3;9:<9??"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9#$45$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,47!$2#28,1#!$2#38,8$24!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8@#4&6$31#2!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#!$2-138,8#42580!$2#48,1#!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#1#3;9:<9??,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV1sp.

Module LibSegNs_teV2an.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [276524].
Definition STOPS1 : list Z := [276524] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4382<#4382<#5=#4382<,20##42704+$2-130$3$4$5$6$7+&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20@-3;9:<:00/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00+$2#48+$2#48+$2#70&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20&8/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00@#100000000/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00@#100000000/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00@#3;9:<:00/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00+$2-78@#4&6$30#2##3;9:<:00#1+$2-78+$2-98+$2#78+$2#58$19#2+$2#28$1<$1=$1>$1?,,3?!$2#58,8&8/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00@#100000000/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00!$2#60,8&8/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00@#100000000/5&6$26#20#3;9:<:00!$2#50,8#2!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 276524 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2an.

Module LibSegNs_teV2ap.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_bebaca.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_bebaca.IT.
Definition ENDS : list Z := [276524].
Definition STOPS1 : list Z := [276524] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4382<#4382<#5=#4382<,20##42704+$2-130$3$4$5$6$7+&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20@-3;9:<:00/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00+$2#48+$2#48+$2#70&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20&8/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00@#100000000/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00@#100000000/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00@#3;9:<:00/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00+$2-78@#4&6$30#2##3;9:<:00#+$2-78+$2-98+$2#78+$2#58$19#+$2#28$1<$1=$1>$1?,,3?!$2#58,8&8/5&8@#100000000%1&6$24#20@#3;9:<:00/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00&6@#100000000$24#20#3;9:<:00@#100000000/5+&6$24#20+@#100000000&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20@^-3-;9:<:0000000000/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00#3;9:<:00!$2#60,8&8/5&8@#100000000%1&6$26#20@#3;9:<:00/5&6$26#20#3;9:<:00&6@#100000000$26#20#3;9:<:00@#100000000/5&6$26#20#3;9:<:00!$2#50,8#2!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 276524 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV2ap.

Module LibSegNs_teV2b00n.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29##'$2:##'$2;##"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9##2#2+$2#58+$2#50#+$2-78$37$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,52!$2#28,1#2!$2#48,1#2!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#1!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#!$2-<8,1#!$2#50,8#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29##'$2:##'$2;##,40!"%pstring).
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
End LibSegNs_teV2b00n.

Module LibSegNs_teV2b00p.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29##'$2:##'$2;##"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9###2+$2#58+$2#50#+$2-78$37$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,52!$2#28,1#!$2#48,1#!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#!$2-<8,1#!$2#50,8#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29##'$2:##'$2;##,40!"%pstring).
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
End LibSegNs_teV2b00p.

Module LibSegNs_teV2b01n.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29##'$2:##'$2;#1^#?#???????????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##2$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,52!$2#28,1#2!$2#48,1#2!$2#38,8$2;!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#1!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#1!$2-<8,1#!$2#50,8#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29##'$2:##'$2;#1^#?#???????????????,50!"%pstring).
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
End LibSegNs_teV2b01n.

Module LibSegNs_teV2b01p.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29##'$2:##'$2;#1^#?#???????????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,52!$2#28,1#!$2#48,1#!$2#38,8$2;!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#1!$2-<8,1#!$2#50,8#'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29##'$2:##'$2;#1^#?#???????????????,50!"%pstring).
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
End LibSegNs_teV2b01p.

Module LibSegNs_teV2b10n.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;##"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9##2#2+$2#58+$2#58$29+$2-78$37$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,52!$2#28,1#2!$2#48,1#2!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#1!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#!$2-<8,1#!$2#50,8#1'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;##,40!"%pstring).
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
End LibSegNs_teV2b10n.

Module LibSegNs_teV2b10p.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;##"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9###2+$2#58+$2#58$29+$2-78$37$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,52!$2#28,1#!$2#48,1#!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#!$2-<8,1#!$2#50,8#1'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;##,40!"%pstring).
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
End LibSegNs_teV2b10p.

Module LibSegNs_teV2b11n.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",44'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#2!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:8,8+$2-78!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-180,8+$2#48!$2-178,8#43460!$2-150,8#2!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42680!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#38,$2-170#20,$2-130#30,$2-?8#50,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;#1^#?#???????????????"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##2$46$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,52!$2#28,1#2!$2#48,1#2!$2#38,8$2;!$2#40,8#!$2#30,8#1!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8#1!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#1!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8#1!$2-158,8#3;9:<:00!$2-150,8#!$2-148,8+$2#48!$2-140,8$2;!$2-138,8#42724!$2-;0,8#!$2-;8,8$2;!$2-<0,8#1!$2-<8,1#!$2#50,8#1'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0($2#8#80!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#58,8$29!$2#60,8$2:!$2#68,1#2!$2#70,8#2!$2#78,8$24!$2#80,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$2>##??'&9$2>#1##'$2?##??'&9$2?#1##!$2-1:0,8#1!$2-198,8#3;9:<:00!$2-190,8#!$2-188,8#2!$2-100,8#1!$2-88,1$2?!$2-:8,1$2>!$2-90,8$26!$2-98,8$24!$2-:0,8#2!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28,$2-1>0#8,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7'$29#1^#?#???????????????'$2:##'$2;#1^#?#???????????????,50!"%pstring).
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
End LibSegNs_teV2b11n.

End BndP_Ns_074.
Module BndP_Ns_073.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Ns_073 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_4f613e2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1n3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX1p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbX2p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDn3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXDp3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_tbXr03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr222BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr223NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr222BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr225XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr222F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr223PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr224planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr225regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_tbXr223kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_388f082ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073=LibSegNs_teN03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teNp23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_bebaca2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073>LibSegNs_teV0p3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0161;BndP_Ns_073?LibSegNs_teV1bn3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_tbX1n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274536].
Definition STOPS1 : list Z := [274536] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23#1##9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#1!$2#10,8$24!$2#18,8#'$24#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
Definition ss0 : sym_state := SS 274504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#43068#43068!#!!,2#43068#43068#5=#43068,20##43064$2$3$4$41$42$43$2:#$22$45$46$47$48$49$4:$4;$23#1##9$2=$17$18$19$1:$1;$4<$4=$4>$4?,,26!$22#10,8$24!$22#,1#2!$22#18,8#!$22#8,8#1!$2-:8,8#9!$2-:0,8#2!$2-98,8$2!$2-90,8#!$2-88,8#1!$2-80,8$22!$2-78,8#43460!$2-50,8#1!$2-48,8#!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#1!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064!$2#,1#2'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#6?%#10000#<6<<0!$2#8,8#1!$2#10,8$24!$2#18,8#'$24#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbX1n.

Module LibSegNs_tbX1p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274536].
Definition STOPS1 : list Z := [274536] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23###9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#1!$2#10,8$24!$2#18,8#'$24#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
Definition ss0 : sym_state := SS 274504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#43068#43068!#!!,2#43068#43068#5=#43068,20##43064$2$3$4$41$42$43$2:#$22$45$46$47$48$49$4:$4;$23###9$2=$17$18$19$1:$1;$4<$4=$4>$4?,,26!$22#10,8$24!$22#,1#!$22#18,8#!$22#8,8#1!$2-:8,8#9!$2-:0,8#!$2-98,8$2!$2-90,8#!$2-88,8#1!$2-80,8$22!$2-78,8#43460!$2-50,8#1!$2-48,8#!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##70%#10000#<6<<0!$2#,1#!$2#8,8#1!$2#10,8$24!$2#18,8#'$24#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbX1p.

Module LibSegNs_tbX2n.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274536].
Definition STOPS1 : list Z := [274536] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23#1##9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
Definition ss0 : sym_state := SS 274504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#43068#43068!#!!,2#43068#43068#5=#43068,20##43064$2$3$4$41$42$43$2:#$22$45$46$47$48$49$4:$4;$23#1##9$2=$17$18$19$1:$1;$4<$4=$4>$4?,,27!$22#10,8$24!$22#18,8$26!$22#,1#2!$22#8,8#2!$2-:8,8#9!$2-:0,8#2!$2-98,8$2!$2-90,8#!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8#2!$2-48,8$26!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#1!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064!$2#,1#2'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#6?%#10000#<6<<0!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbX2n.

Module LibSegNs_tbX2p.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274536].
Definition STOPS1 : list Z := [274536] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23###9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
Definition ss0 : sym_state := SS 274504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#43068#43068!#!!,2#43068#43068#5=#43068,20##43064$2$3$4$41$42$43$2:#$22$45$46$47$48$49$4:$4;$23###9$2=$17$18$19$1:$1;$4<$4=$4>$4?,,27!$22#10,8$24!$22#18,8$26!$22#,1#!$22#8,8#2!$2-:8,8#9!$2-:0,8#!$2-98,8$2!$2-90,8#!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8#2!$2-48,8$26!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##70%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbX2p.

Module LibSegNs_tbXDn.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274536].
Definition STOPS1 : list Z := [274536] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23#1##9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#2!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#)$29##40$22##20'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
Definition ss0 : sym_state := SS 274504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#43068#43068!#!!,2#43068#43068#5=#43068,20##43064$2$3$4$41$42$43$2:#$22$45$46$47$48$49$4:$4;$23#1##9$2=$17$18$19$1:$1;$4<$4=$4>$4?,,2?!$22#10,8$24!$22#18,8$26!$22#,1#2!$22#8,8#2!$2-:8,8#9!$2-:0,8#3!$2-98,8$2!$2-90,8#!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8#2!$2-48,8$29!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#1!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064!$2#,1#3'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#6?%#10000#<6<<0!$2#8,8#2!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#)$29##40$22##20'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbXDn.

Module LibSegNs_tbXDp.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274536].
Definition STOPS1 : list Z := [274536] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23###9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#2!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#)$29##40$22##20'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
Definition ss0 : sym_state := SS 274504 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 34), (0), ELit 32)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 34), (0), 32)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#43068#43068!#!!,2#43068#43068#5=#43068,20##43064$2$3$4$41$42$43$2:#$22$45$46$47$48$49$4:$4;$23###9$2=$17$18$19$1:$1;$4<$4=$4>$4?,,2?!$22#10,8$24!$22#18,8$26!$22#,1#!$22#8,8#2!$2-:8,8#9!$2-:0,8#1!$2-98,8$2!$2-90,8#!$2-88,8#2!$2-80,8$22!$2-78,8#43460!$2-50,8#2!$2-48,8$29!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##70%#10000#<6<<0!$2#,1#1!$2#8,8#2!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#)$29##40$22##20'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274536 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbXDp.

Module LibSegNs_tbXr0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [271312].
Definition STOPS1 : list Z := [271312] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$5$6$7$2:#$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16"%pstring).
Definition ss0 : sym_state := SS 274568 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9$2:#$33$34$35$36$37$38$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271312 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274568 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274568 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbXr0.

Module LibSegNs_tbXr22.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [271312].
Definition STOPS1 : list Z := [271312] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$5$6$7$2:#16$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16"%pstring).
Definition ss0 : sym_state := SS 274568 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9$2:#16$33$34$35$36$37$38$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271312 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274568 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274568 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbXr22.

Module LibSegNs_teN0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_388f08.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_388f08.IT.
Definition ENDS : list Z := [271436].
Definition STOPS1 : list Z := [271436] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800040#800000000000&$2#10($2-30#30'$22#7???7?800000#7?????????>0&$22#8)$2-30#30$22##20!$22#,1$25!$22#8,8#!$22#10,8$24!$22#18,8$26'$25##??'&9$25#1##"%pstring).
Definition ss0 : sym_state := SS 271324 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4244<#4244<#5=#4244<,20#$28$2$3$4$5$6$7$8$9##+$22#10$25##+$2-20#$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,12!$2-18,8#!$2-20,8#!$2-28,8#!$2-30,1#!$2-10,8$8!$2-8,8$28'$2#7???7?800040#800000000000&$2#10($2-30#30'$22#7???7?800000#7?????????>0&$22#8)$2-30#30$22##20!$22#,1$25!$22#8,8#!$22#10,8$24!$22#18,8$26'$25##??'&9$25#1##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_388f08.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271324 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_388f08.IT BndT_Ns_000.SegItab_Ns_388f08.IT_sound BF NX0 BR XSTEP F0 PSS plan 271324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teN0.

Module LibSegNs_teNp0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_388f08.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_388f08.IT.
Definition ENDS : list Z := [271436].
Definition STOPS1 : list Z := [271436] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-30#30'$22#7???7?800000#7?????????>0&$22#8)$2-30#30$22##20!$22#,1$25!$22#8,8$27!$22#10,8$24!$22#18,8$26'$25##??'&9$25#1##'$27#1#2'&9$25#2##"%pstring).
Definition ss0 : sym_state := SS 271324 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4244<#4244<#5=#4244<,20#$28$2$3$4$5$6$7$8$9#1#+$22#10#$27#+$2-20#$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-18,8#!$2-20,8#!$2-28,8#!$2-30,1#!$2-10,8$8!$2-8,8$28'$2#7???7?800040#800000000000&$2#10($2-30#30'$22#7???7?800000#7?????????>0&$22#8)$2-30#30$22##20!$22#,1$25!$22#8,8$27!$22#10,8$24!$22#18,8$26'$25##??'&9$25#1##'$27#1#2'&9$25#2##,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_388f08.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271324 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_388f08.IT BndT_Ns_000.SegItab_Ns_388f08.IT_sound BF NX0 BR XSTEP F0 PSS plan 271324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teNp0.

Module LibSegNs_teNp2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_388f08.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_388f08.IT.
Definition ENDS : list Z := [271436].
Definition STOPS1 : list Z := [271436] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 40; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 34; ELit 0; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?800040#800000000000&$2#10($2-30#30'$22#7???7?800000#7?????????>0&$22#8)$2-30#30$22##20!$22#,1$25!$22#8,8$27!$22#10,8$24!$22#18,8$26'$25##??'&9$25#1##'$27#1#2'&9$25#2#2#2"%pstring).
Definition ss0 : sym_state := SS 271324 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4244<#4244<#5=#4244<,20#$28$2$3$4$5$6$7$8$9#1#+$22#10#1$27#+$2-20#$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-18,8#!$2-20,8#!$2-28,8#!$2-30,1#!$2-10,8$8!$2-8,8$28'$2#7???7?800040#800000000000&$2#10($2-30#30'$22#7???7?800000#7?????????>0&$22#8)$2-30#30$22##20!$22#,1$25!$22#8,8$27!$22#10,8$24!$22#18,8$26'$25##??'&9$25#1##'$27#1#2'&9$25#2#2#2,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 271436 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_388f08.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271324 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_388f08.IT BndT_Ns_000.SegItab_Ns_388f08.IT_sound BF NX0 BR XSTEP F0 PSS plan 271324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teNp2.

Module LibSegNs_teV0n.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#!$2#78,8#!$2#80,8#"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9###2###1+$2-78@#4&6$30#2$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,46!$2#28,1#2!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8&9+@#4&6$31#2#2#?=!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42580!$2#48,1#2!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8#!$2-98,8#!$2-:0,8#!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#!$2#78,8#!$2#80,8#,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV0n.

Module LibSegNs_teV0p.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#!$2#78,8#!$2#80,8#"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$5$6$7$8$9###2###1+$2-78@#4&6$30#2$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,46!$2#28,1#!$2#30,8#!$2-1=8,8+$2-78!$2-1=0,8@#4&6$31#2!$2-1<8,8+$2-:8!$2-1<0,8#!$2-1;8,8#!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8#!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#!$2-138,8#42580!$2#48,1#!$2#50,8#!$2-;0,8#!$2-;8,8#!$2-<0,8#!$2-<8,1#!$2-88,1@#4&6$30#2!$2-:8,1@#4&6$31#2!$2-90,8#!$2-98,8#!$2-:0,8#!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#68,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#58,8#!$2#60,8#!$2#68,1#!$2#70,8#!$2#78,8#!$2#80,8#,40!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV0p.

Module LibSegNs_teV1bn.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28$2$3$4$5$6$7$8$9+$2#68+$2#8+$2#48+$2#28#1$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#1>0($2#8#80!$2-88,1$30!$2-:8,1$31'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#30,8#!$2#38,8#!$2#40,8#!$2#48,1#!$2#50,8#!$2#58,8#!$2#60,8#!$2#68,1#2!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 271440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5;#43464,20##43460+$2-1:0$3$4$41$42$43+$2#28&4#/7$24#3;9:<:00###2$47$48$49$4:$4;#+$2-<8#+$2-78+$2-98+$2#78+$2#58$19#2+$2#28$4<$4=$4>$4?,,49!$2#30,8&4#/7$24#3;9:<:00!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24#3;9:<:00!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24#3;9:<:00!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24#3;9:<:00!$2-<0,8&4#/7$24#3;9:<:00!$2-<8,1#!$2#58,8/5$24#3;9:<:00!$2#48,1#!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#28,1#!$2#38,8#!$2#40,8#!$2#68,1#2!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ce2 : expr := EMd Instr.M_REMU (EVar 36) (ELit 1000000000).
Definition arms2 := Eval vm_compute in (SGP.case_arms s1 ce2 (0)).
Definition lo2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition hi2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$41$42$43$8$9##2#2$47$48$49$4:$4;$12$13$14$15$16$17$18$19$1:$1;$4<$4=$4>$4?,,4:!$2#28,1#2!$2#48,1#2'/7$24#3;9:<:00##!$2#30,8&4#/7$24#3;9:<:00!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24#3;9:<:00!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24#3;9:<:00!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24#3;9:<:00!$2-<0,8&4#/7$24#3;9:<:00!$2-<8,1#!$2#58,8/5$24#3;9:<:00!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#38,8#!$2#40,8#!$2#68,1#2!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",3!!,2#42:18#42:18!#!!,2#42:18#42:18#5=#42:18,20#$28$2$3$4$51$52$53$8$9##2$56$57$58$59$5:$5;$12$13$14$15$16$17$18$19$1:$1;$5<$5=$5>$5?,,4:!$2#28,1#2!$2#48,1#2!$2#38,8/7$24#3;9:<:00!$2#40,8#'/7$24#3;9:<:00#1#3;9:<9??!$2#30,8&4#/7$24#3;9:<:00!$2-1=8,8+$2-78!$2-1=0,8#!$2-1<8,8+$2-<8!$2-1<0,8#!$2-1;8,8&4#/7$24#3;9:<:00!$2-1;0,8+$2#28!$2-1:8,8#43460!$2-180,8&4#/7$24#3;9:<:00!$2-178,8#!$2-170,8+$2#28!$2-168,8#433=0!$2-160,8+$2-78!$2-158,8#1!$2-150,8+$2#68!$2-148,8+$2#48!$2-140,8#1!$2-138,8#42634!$2-;0,8#!$2-;8,8/7$24#3;9:<:00!$2-<0,8&4#/7$24#3;9:<:00!$2-<8,1#!$2#58,8/5$24#3;9:<:00!$2#60,8#!$2#50,8#1!$2-100,8#1!$2-88,1@#4&6$30#2!$2-:8,1&9+@#4&6$31#2#2#?=!$2-90,8#!$2-98,8$24!$2-:0,8#1!$2-70,8#!$2-78,8#3;9:<:00!$2-80,8#1!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$28'$2#7???7?8001>0#7?????????78&$2#10($2-1>0#1>0,$2-1>0#8,$2-1:0#20,$2-130#30,$2-?8#30,$2-<7#7,$2-:7#7,$2-87#7($2#8#80'$30##??'$31##??!$2#8,1#!$2#10,8#1!$2#18,8#3;9:<:00!$2#20,8#!$2#68,1#2!$2#70,8#1!$2#78,8$24!$2#80,8#'$24#3;9:<:01^#?#???????????????,60!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_bebaca.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_bebaca.IT BndT_Ns_002.SegItab_Ns_bebaca.IT_sound BF NX0 BR XSTEP F0 PSS plan 271440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_teV1bn.

End BndP_Ns_073.
