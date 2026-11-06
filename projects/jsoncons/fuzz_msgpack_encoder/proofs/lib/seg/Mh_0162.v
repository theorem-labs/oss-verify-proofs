(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000 BndT_Ns_002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Ns_070.
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
Ltac2 kr_t_BndP_Ns_070 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_05133d2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_srD3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_srE23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_002ASegItab_Ns_fc98e52ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svD33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_svH13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svQ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070<LibSegNs_svR3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_4f613e2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_070=LibSegNs_tbA03kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_srD.
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
   KWord (SA (EVar 36) (288)) 8 (EVar 33);
   KUnk (SA (EVar 36) 256) (ELit 8);
   KWr (SA (EVar 36) 256) (ELit 40);
   KWord (SA (EVar 2) (-8)) 8 (EVar 40);
   KWord (SA (EVar 2) (-16)) 8 (EVar 41);
   KWord (SA (EVar 2) (-24)) 8 (EVar 42);
   KWord (SA (EVar 2) (-32)) 8 (EVar 43);
   KWord (SA (EVar 2) (-40)) 8 (EVar 44);
   KRange (EVar 33) 1 16384;
   KRange (EVar 38) 1 16383;
   KRange (APC.esub (EVar 33) (EVar 38)) 0 16383;
   KRange (EVar 39) 0 16383;
   KRange (EVar 35) 4096 140737488338944].
Definition ss0 : sym_state := SS 287572 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46418#46418#5=#46418,20#$28$2$3$4$5$6$7$29$2:+$26$27+$21@-1$26+$26$30$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,16!$24#120,8+$21@-1$26!$24#118,8+$23$26!$24#100,8+$26$30'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000($24#100#28!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21#1#4000'$26#1#3???'+$21@-1$26##3???'$27##3???'$23#1000#7???????<000,31!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287572 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287572 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srD.

Module LibSegNs_srE1.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24##4000$;$<$=$>$?$10$11$25#4000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<"%pstring).
Definition ss0 : sym_state := SS 287668 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46418#46418#5=#46418,20#$28$2$3$4$5$6$7$29$2:#4000$;$<$=$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$24#100,8+$30#4000'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<,31!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287668 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287668 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srE1.

Module LibSegNs_srE2.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$24#$21$;$<$=$>$?$10$11$25#4000$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#,$24#100#8($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#98,4#!$2=#9<,4#!$2=#:0,8+$2=#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21##3???($2=#98#4"%pstring).
Definition ss0 : sym_state := SS 287668 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-48), ELit 48); ((EVar 36), (256), ELit 40); ((EVar 45), (152), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-48), 48); ((EVar 36), (256), 40); ((EVar 45), (152), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#46418#46418#5=#46418,20#$28$2$3$4$5$6$7$29$2:$21#2##$>$?$10$11$2;$2<$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$24#100,8+$21$30!$2=#98,4#2'$2#7???7?800030#800000000000&$2#10($2-30#30'$24#7???7?800030#7????????>=8&$24#8)$2-30#30$24##128!$24#108,8$22!$24#110,8#4000!$24#118,8$23!$24#120,8#($24#100#28'$2=#7???7?800030#7????????>?0&$2=#8)$2-30#30$2=##110%#10000#<6<<0)$24##128$2=##110!$24#?0,8$2=!$24#?8,8+$2=#10!$2=#,8#<3688!$2=#10,8#<3598!$2=#9<,4#!$2=#:0,8+$2=#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<'$21##3???($2=#98#4,31!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_05133d.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 287668 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_05133d.IT BndT_Ns_000.SegItab_Ns_05133d.IT_sound BF NX0 BR XSTEP F0 PSS plan 287668 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_srE2.

Module LibSegNs_svA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291376; 291636].
Definition STOPS1 : list Z := [291376; 291636] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); (EVar 35); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332483136 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64);
   KRange (EVar 35) 0 18446744073709551615].
Definition ss0 : sym_state := SS 291320 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#47230#47334#47230#47334#5;#47220,20#$1+$2-40$3$4$5$6$7$23$9$21$22$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,<!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#47230#47334#47230#47334#5=#47334,20#$1$2$3$4$5$6$7$8$9$23$22$23$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,='&4&1$23##1#1#1!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#47230#47334#47230#47334#5=#47230,20#$1+$2-40$3$4$5$6$7$23$22$21$22$23$=$>$?$10$11$21$13$14$23$16$17$18$19$1:$1;$1<$1=$1>$1?,,='&4&1$23##1##!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?800040#800000000000&$2#10($2-40#40'$23#^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 291636 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svA.

Module LibSegNs_svD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291640].
Definition STOPS1 : list Z := [291640] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21#4000$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$27!$22#8,8+$27$28'$27##800000000000'$28##8008000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291504 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47338#47338#5=#47338,20##472<8+$2-40$3$4$5$6$7$23$22$22+$28#4000$<$=$>$?$10$11$21#4000$28$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$27!$22#8,8+$27$28'$27##800000000000'$28##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291640 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291504 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291504 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svD.

Module LibSegNs_svD2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291092].
Definition STOPS1 : list Z := [291092] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21#4000$2;$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$29'$29#1000#800000000000'$2;##8008000"%pstring).
Definition ss0 : sym_state := SS 291528 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47114#47114#5=#47114,20##472=<+$2-40$3$4$5$6$7$23$22$21+$29$2;#4000$=$>$?$10$11$21#4000$2;$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$29'$29#1000#800000000000'$2;##8008000,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291528 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291528 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svD2.

Module LibSegNs_svD3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291640; 291376; 291636].
Definition STOPS1 : list Z := [291640; 291376; 291636] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$35$;$<$=$>$?$10$11$21#4000$2;$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",13'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128,$21#100#8($21#100#8'$35##4000'$2;##8008000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291548 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (256), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (256), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5;#472>8,20#$1+$2-40$3$4$5$6$7$23$22$35+$35$38$<$=$>$?$10$11$21#4000$2;$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,13!$21#100,8+$35$38'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128($21#100#8'$35##4000'$2;##8008000'$24#1^#?#???????????????,39!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5;#472:8,20#$1+$2-40$3$4$5$6$7$23$22$35+$35$38$<$=$>$?$10$11$21#4000$2;+$24-4000$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4&1$35#4000#1#1#1!$21#100,8+$35$38'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128($21#100#8'$35##4000'$2;##8008000'$24#1^#?#???????????????,39!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5=#47334,20#$2<$2$3$4$5$6$7$2=$2>++$23@-1$24#4000+$35$38$<$=$>$?$10$11$2?$30$31$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,15'&4&1+$24-4000##1#1#1'&4&1$35#4000#1#1#1!$21#100,8+$35$38'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128($21#100#8'$35##4000'$2;##8008000'$24#1^#?#???????????????,39!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5=#47230,20#$1+$2-40$3$4$5$6$7$23$22$35+$35$38$<$=$>$?$10$11$21#4000$2;+$24-4000$16$17$18$19$1:$1;$1<$1=$1>$1?,,15'&4&1+$24-4000##1##'&4&1$35#4000#1#1#1!$21#100,8+$35$38'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128($21#100#8'$35##4000'$2;##8008000'$24#1^#?#???????????????,39!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5=#47338,20##47304+$2-40$3$4$5$6$7$23$22$22+$2;$35$<$=$>$?$10$11$21$35$2;$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,14'&4&1$35#4000#1##!$21#100,8+$35$38'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128($21#100#8'$35##4000'$2;##8008000'$24#1^#?#???????????????,39!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 291640 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 291376 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 291636 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291548 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291548 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svD3.

Module LibSegNs_svE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291640; 291376; 291636].
Definition STOPS1 : list Z := [291640; 291376; 291636] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$35$;$<$=$>$?$10$11$21#4000$2:$24$2;$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$35##4000'$2:#1#4000'$2;##8008000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5;#472:0,20#$1+$2-40$3$4$5$6$7$23$22$35$;$<$=$>$?$10$11$21$2:$2:$24$2;$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$35##4000'$2:#1#4000'$2;##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5;#472:8,20#$1+$2-40$3$4$5$6$7$23$22$35$;$<$=$>$?$10$11$21$2:$2:+$24@-1$2:$2;$17$18$19$1:$1;$1<$1=$1>$1?,,10'&4&1$35$2:#1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$35##4000'$2:#1#4000'$2;##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5=#47334,20#$2<$2$3$4$5$6$7$2=$2>+$23+@-1$24$2:$;$<$=$>$?$10$11$2?$30$31$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,11'&4&1+$24@-1$2:##1#1#1'&4&1$35$2:#1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$35##4000'$2:#1#4000'$2;##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5=#47230,20#$1+$2-40$3$4$5$6$7$23$22$35$;$<$=$>$?$10$11$21$2:$2:+$24@-1$2:$2;$17$18$19$1:$1;$1<$1=$1>$1?,,11'&4&1+$24@-1$2:##1##'&4&1$35$2:#1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$35##4000'$2:#1#4000'$2;##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47338#47230#47334#47338#47230#47334#5=#47338,20##47304+$2-40$3$4$5$6$7$23$22$22+$2;$35$<$=$>$?$10$11$21$35$2:$24$2;$17$18$19$1:$1;$1<$1=$1>$1?,,10'&4&1$35$2:#1##'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$35##4000'$2:#1#4000'$2;##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 2)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 0))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 291640 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 291376 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 291636 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svE.

Module LibSegNs_svF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291376; 291636].
Definition STOPS1 : list Z := [291376; 291636] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$2:##4000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291588 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#47230#47334#47230#47334#5;#472:8,20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14+$24@-1$2:$16$17$18$19$1:$1;$1<$1=$1>$1?,,='$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$2:##4000'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#47230#47334#47230#47334#5=#47334,20#$2<$2$3$4$5$6$7$2=$2>+$23+@-1$24$2:$;$<$=$>$?$10$11$2?$30$31$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,>'&4&1+$24@-1$2:##1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$2:##4000'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#47230#47334#47230#47334#5=#47230,20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$2:$14+$24@-1$2:$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'&4&1+$24@-1$2:##1##'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$2:##4000'$24#1^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291376 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 291636 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291588 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291588 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svF.

Module LibSegNs_svH0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291428; 291504; 291636].
Definition STOPS1 : list Z := [291428; 291504; 291636] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$13$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",19'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128%#10000#<6<<0!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800040#7????????>?0&$26#8)$2-40#40$26##110!$26#,8#<3688!$26#98,1$34'$34##2'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291376 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47264#472;0#47334#47264#472;0#47334#5;#47258,20#$1+$2-40$3$4$5$6$7$23$22@#2&6$34#1#78$<$=$>$?$10$11$21$13$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,19'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128%#10000#<6<<0!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800040#7????????>?0&$26#8)$2-40#40$26##110!$26#,8#<3688!$26#98,1$34'$34##2'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47264#472;0#47334#47264#472;0#47334#5;#47260,20#$1+$2-40$3$4$5$6$7$23$22@#2&6$34#1#78$<$=$>$?$10$11$21#4000$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4&1@#2&6$34#1##1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128%#10000#<6<<0!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800040#7????????>?0&$26#8)$2-40#40$26##110!$26#,8#<3688!$26#98,1$34'$34##2'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47264#472;0#47334#47264#472;0#47334#5=#47264,20#$1+$2-40$3$4$5$6$7$23$22@#2&6$34#1#78$<$=$>$?$10$11$21#4000$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4$24#4000#1#1'&4&1@#2&6$34#1##1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128%#10000#<6<<0!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800040#7????????>?0&$26#8)$2-40#40$26##110!$26#,8#<3688!$26#98,1$34'$34##2'$24#1^#?#???????????????,38!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47264#472;0#47334#47264#472;0#47334#5=#472;0,20#$1+$2-40$3$4$5$6$7$23$22@#2&6$34#1#78$<$=$>$?$10$11$21#4000$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4$24#4000##'&4&1@#2&6$34#1##1#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128%#10000#<6<<0!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800040#7????????>?0&$26#8)$2-40#40$26##110!$26#,8#<3688!$26#98,1$34'$34##2'$24#1^#?#???????????????,38!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#47264#472;0#47334#47264#472;0#47334#5=#47334,20#$2<$2$3$4$5$6$7$2=$2>+$23@-1$24#78$<$=$>$?$10$11$2?$30$31$32$33$17$18$19$1:$1;$1<$1=$1>$1?,,1:'&4&1@#2&6$34#1##1##'$2#7???7?800040#800000000000&$2#10($2-40#40!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31!$2-38,8$32!$2-40,8$33'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128%#10000#<6<<0!$21#120,8#!$21#110,8#4000!$21#?0,8$26'$26#7???7?800040#7????????>?0&$26#8)$2-40#40$26##110!$26#,8#<3688!$26#98,1$34'$34##2'$24#1^#?#???????????????,38!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 291428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 291504 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 291636 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291376 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291376 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svH0.

Module LibSegNs_svH1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291428].
Definition STOPS1 : list Z := [291428] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21$13$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800040#800000000000&$2#10($2-40#40'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128!$21#120,8$25'$25#1#4000!$21#110,8#4000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291376 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47264#47264#5=#47264,20#$1+$2-40$3$4$5$6$7$23$22$25$;$<$=$>$?$10$11$21#4000$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800040#800000000000&$2#10($2-40#40'$21#7???7?800040#7????????>=8&$21#8)$2-40#40$21##128!$21#120,8$25'$25#1#4000!$21#110,8#4000'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 291428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291376 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291376 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svH1.

Module LibSegNs_svQ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [287388].
Definition STOPS1 : list Z := [287388] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21#4000$2:$24$2;$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$29'$29#1000#800000000000'$2:#1#4000'$2;##8008000"%pstring).
Definition ss0 : sym_state := SS 291464 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4629<#4629<#5=#4629<,20##4729<+$2-40$3$4$5$6$7$23$22$21+$29$2;$2:$=$>$?$10$11$21#4000$2:$24$2;$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$29'$29#1000#800000000000'$2:#1#4000'$2;##8008000,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291464 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291464 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svQ.

Module LibSegNs_svR.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_002.SegItab_Ns_fc98e5.ITR.
Definition IT : itab := BndT_Ns_002.SegItab_Ns_fc98e5.IT.
Definition ENDS : list Z := [291640].
Definition STOPS1 : list Z := [291640] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21#4000$14$24$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$27!$22#8,8+$27$28'$27##800000000000'$28##8008000'$24#1^#?#???????????????"%pstring).
Definition ss0 : sym_state := SS 291428 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47338#47338#5;#47268,20#$1+$2-40$3$4$5$6$7$23$22$:$;$<$=$>$?$10$11$21#4000$24$24$16$17$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$27!$22#8,8+$27$28'$27##800000000000'$28##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47338#47338#5=#47338,20##47288+$2-40$3$4$5$6$7$23$22$22+$24$28$<$=$>$?$10$11$21#4000$24$24$28$17$18$19$1:$1;$1<$1=$1>$1?,,<'&4$24#4000#1#1'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$27!$22#8,8+$27$28'$27##800000000000'$28##8008000'$24#1^#?#???????????????,38!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#47338#47338#5=#47338,20##47288+$2-40$3$4$5$6$7$23$22$22+$28#4000$<$=$>$?$10$11$21#4000#4000$24$28$17$18$19$1:$1;$1<$1=$1>$1?,,<'&4$24#4000##'$2#7???7?800040#800000000000&$2#10($2-40#40'$22#7???7?800040#7?????????>8&$22#8)$2-40#40$22##18!$22#,8$27!$22#8,8+$27$28'$27##800000000000'$28##8008000'$24#1^#?#???????????????,38!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 291640 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 291640 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_002.SegItab_Ns_fc98e5.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 291428 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_002.SegItab_Ns_fc98e5.IT BndT_Ns_002.SegItab_Ns_fc98e5.IT_sound BF NX0 BR XSTEP F0 PSS plan 291428 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_svR.

Module LibSegNs_tbA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274492].
Definition STOPS1 : list Z := [274492] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#!$2#10,8#!$2#18,8#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5;#43860,20##43324+$2-60$3$4$39$3:$3;$2&9$2=#?$2##1+$2#10+$2#10&9$2=#?$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,22!$2#10,8&9$2=#?!$2#18,8#!$2#8,8#1!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#!$2-;8,8#1!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5=#4303<,20##4303<$2$3$4$39$3:$3;$2:$22$2##+$2#10+$2#8&9$2=#?$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,23!$2#,1#!$2#8,8#'&4&1&9$2=#?##1#1#1!$2#10,8&9$2=#?!$2#18,8#!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#!$2-;8,8#1!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2#1#7,$2#20#50%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5=#4303<,20##4303<$2$3$4$39$3:$3;$2:$22$2##1+$2#10+$2#10&9$2=#?$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,23'&4&1&9$2=#?##1##!$2#10,8&9$2=#?!$2#18,8#!$2#8,8#1!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#!$2-;8,8#1!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274492 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 274492 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274480 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbA0.

End BndP_Ns_070.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Ns_000.
Module BndP_Ns_071.
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
Ltac2 kr_t_BndP_Ns_071 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_4f613e2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbA13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071>LibSegNs_tbA2g3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAr3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbAt3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071<LibSegNs_tbE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFh3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbFl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHb3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbHs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLe3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbLm3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_071=LibSegNs_tbM13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_tbA1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274492].
Definition STOPS1 : list Z := [274492] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#1!$2#10,8$24!$2#18,8#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5;#432?0,20##4323<+$2-60$3$4$39$3:$3;$2+$24&9$2=#?#2+$2#10&4+$24&9$2=#?$24#2$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,23!$2#10,8+$24&9$2=#?!$2#18,8#!$2#8,8#2!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#1!$2-;8,8#2!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5;#43860,20##43324+$2-60$3$4$39$3:$3;$2+$24&9$2=#?$2##1+$2#10+$2#10+$24&9$2=#?$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,24!$2#8,8#1'&4&1&4+$24&9$2=#?$24##1#1#1!$2#10,8+$24&9$2=#?!$2#18,8#!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#1!$2-;8,8#2!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5=#4303<,20##4303<$2$3$4$39$3:$3;$2:$22$2##+$2#10+$2#8+$24&9$2=#?$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,25!$2#,1#!$2#8,8#'&4&1+$24&9$2=#?##1#1#1'&4&1&4+$24&9$2=#?$24##1#1#1!$2#10,8+$24&9$2=#?!$2#18,8#!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#1!$2-;8,8#2!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2#1#7,$2#20#50%#10000#<6<<0'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5=#4303<,20##4303<$2$3$4$39$3:$3;$2:$22$2##1+$2#10+$2#10+$24&9$2=#?$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,25'&4&1+$24&9$2=#?##1##!$2#8,8#1'&4&1&4+$24&9$2=#?$24##1#1#1!$2#10,8+$24&9$2=#?!$2#18,8#!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#1!$2-;8,8#2!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5=#4303<,20##4303<$2$3$4$39$3:$3;$2:$22$2##2+$2#10+$2#18#1$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,24!$2#18,8#1'&4&1&4+$24&9$2=#?$24##1##!$2#10,8+$24&9$2=#?!$2#8,8#2!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#1!$2-;8,8#2!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274492 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 274492 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 274492 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274480 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbA1.

Module LibSegNs_tbA2g.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [275516].
Definition STOPS1 : list Z := [275516] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4343<#4343<#5=#4343<,20##4323<+$2-60$3$4$39$3:$3;$2&9$2=#?$2#3$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,16!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#178,$2##70%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274480 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbA2g.

Module LibSegNs_tbAD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [761592].
Definition STOPS1 : list Z := [761592] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#2!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1)$29##40$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274480 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9>?8#;9>?8#5=#;9>?8,20##4323<+$2-60$3$4$39$3:$3;$2&9$2=#?+$29#10##8$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,2<!$2#8,8#3!$2-=8,8#9!$2-=0,8$2<!$2-<8,8$2;!$2-<0,8#2!$2-;8,8#3!$2-;0,8$2!$2-:8,8#43460!$2-80,8$23!$2-78,8&9$2=#?!$2-70,8$2!$2-68,8#4323<!$2-18,8$22!$2-10,8$2:!$2-8,8#4303<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#;8,$2-:0#20,$2-60#48,$2##8,$2#10#60%#10000#<6<<0!$2#,1#1!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1)$29##40$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274480 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274480 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbAD.

Module LibSegNs_tbAr.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274492].
Definition STOPS1 : list Z := [274492] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##43324+$2-60$3$4$5$6$7$2$32$2$33$34$35$36$37$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#?#???????????????!$2-8,8#4303<!$2-10,8$2:!$2-18,8$22'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4303<#4303<#5=#4303<,20##4303<$2$3$4$5$6$7$2:$22$2#1#2$29+$29#8$26$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$2#8,8#2'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#198,$2#10#60%#10000#<6<<0!$2#,1#1!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#?#???????????????!$2-8,8#4303<!$2-10,8$2:!$2-18,8$22'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274492 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbAr.

Module LibSegNs_tbAt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [276524].
Definition STOPS1 : list Z := [276524] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30+$2-60$3$4$5$6$7$2$2>$31$33$34$35$36$37$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#4#!$2-8,8#4303<!$2-10,8$2:!$2-18,8$22'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39'$2>##9"%pstring).
Definition ss0 : sym_state := SS 275004 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4382<#4382<#5;#432?0,20#$30+$2-60$3$4$5$6$7$2+$24$2>#3$29&4+$24$2>$24#2$36$37$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,1:!$29#,8+$24$2>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#4#!$2-8,8#4303<!$2-10,8$2:!$2-18,8$22'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39'$2>##9,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4382<#4382<#5=#4382<,20##43324+$2-60$3$4$5$6$7$2+$24$2>$2$29&4+$24$2>$24#2$36$37$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,1;'&4&1&4+$24$2>$24##1#1#1!$29#,8+$24$2>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#4#!$2-8,8#4303<!$2-10,8$2:!$2-18,8$22'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39'$2>##9,40!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4382<#4382<#5=#4382<,20##43324+$2-60$3$4$5$6$7$2+$24$2>$2+$29#10#3#$36$37$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,1;!$29#8,8+$26#1'&4&1&4+$24$2>$24##1##!$29#,8+$24$2>'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#4#!$2-8,8#4303<!$2-10,8$2:!$2-18,8$22'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39'$2>##9,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 276524 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 276524 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 275004 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 275004 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbAt.

Module LibSegNs_tbE.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##423<0$2$3$4$5$6$7$2:$22$31#30$33$22$>$?$10$11$23$2;$2<$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9$2:##2$22$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,32!$22#8,8#!$2-:8,8$15!$2-:0,8#!$2-98,8$2!$2-90,8#!$2-88,8#!$2-80,8$22!$2-78,8#43460!$2-50,8#!$2-48,8#!$2-40,8$22!$2-38,8#433=0!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#42?;4!$2#18,8#!$2#10,8#!$2#8,8#!$2#,1#'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#7,$2#20#50%#10000#<6<<0'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#10,8#!$22#18,8#!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbE.

Module LibSegNs_tbFh.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2?$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 35) 1 140737488355327;
   KWord (SA (EVar 35) 0) 1 (EVar 45);
   KRange (EVar 45) 58 255;
   KDisj (SA (EVar 2) (-400)) (ELit 512) (SA (EVar 35) 0) (ELit 1);
   KRange (EVar 42) 0 140737488355328;
   KRange (EVar 43) 0 1;
   KRange (EVar 44) 1 31].
Definition ss0 : sym_state := SS 274456 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43068#43068#5=#43068,20#$30$2$3$4$39$3:$3;$23#16+$2=-30$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,7'$23#1#7???????????!$23#,1$2='$2=#3:#??)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbFh.

Module LibSegNs_tbFl.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2?$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 35) 1 140737488355327;
   KWord (SA (EVar 35) 0) 1 (EVar 45);
   KRange (EVar 45) 0 47;
   KDisj (SA (EVar 2) (-400)) (ELit 512) (SA (EVar 35) 0) (ELit 1);
   KRange (EVar 42) 0 140737488355328;
   KRange (EVar 43) 0 1;
   KRange (EVar 44) 1 31].
Definition ss0 : sym_state := SS 274456 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43068#43068#5=#43068,20#$30$2$3$4$39$3:$3;$23#16+$2=-30$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,7'$23#1#7???????????!$23#,1$2='$2=##2?)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbFl.

Module LibSegNs_tbHb.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274456].
Definition STOPS1 : list Z := [274456] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##423<0$2$3$4$5$6$7$2:$22$31#30$33$22$>$?$10$11$23$2;$2<$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484096 140737488355184;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-400)) (ELit 512);
   KUnk (SA (EVar 2) (-400)) (ELit 512);
   KImg 65536 814272;
   KRange (EVar 42) 0 140737488355328;
   KRange (EVar 43) 0 1;
   KRange (EVar 44) 10 31].
Definition ss0 : sym_state := SS 274312 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43018#43018#5=#43018,20##4300<$2$3$4$5$6$7$2:$22###2$22$>$?$10$11$23$2;$2<#9$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-38,8$15!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#4300<!$2#18,8#!$2#10,8#!$2#8,8#!$2#,1#'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#158,$2#1#7,$2#20#50%#10000#<6<<0'$2:##800000000000'$2;##1'$2<#:#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274456 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274312 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274312 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbHb.

Module LibSegNs_tbHs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274456].
Definition STOPS1 : list Z := [274456] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##423<0$2$3$4$5$6$7$2:$22$31#30$33$22$>$?$10$11$23$2;$2<$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332484096 140737488355184;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-400)) (ELit 512);
   KUnk (SA (EVar 2) (-400)) (ELit 512);
   KImg 65536 814272;
   KRange (EVar 42) 0 140737488355328;
   KRange (EVar 43) 0 1;
   KRange (EVar 44) 1 9].
Definition ss0 : sym_state := SS 274312 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43018#43018#5=#43018,20##4300<$2$3$4$5$6$7$2:$22###2$22$>$?$10$11$23$2;$2<#9$16$17$18$19$1:$1;$1<$1=$1>$1?,,15!$2-38,8$15!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#4300<!$2#18,8#!$2#10,8#!$2#8,8#!$2#,1#'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#158,$2#1#7,$2#20#50%#10000#<6<<0'$2:##800000000000'$2;##1'$2<#1#9,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274456 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274312 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274312 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbHs.

Module LibSegNs_tbLe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274504].
Definition STOPS1 : list Z := [274504] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;#1#9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 35) 1 140737488355327].
Definition ss0 : sym_state := SS 274492 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43048#43048#5=#43048,20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38+$23#1$2;##9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,1'$23#1#7???????????,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274504 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274492 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274492 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbLe.

Module LibSegNs_tbLm.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274456].
Definition STOPS1 : list Z := [274456] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 44) 2 31;
   KRange (EVar 35) 1 140737488355327].
Definition ss0 : sym_state := SS 274492 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43018#43018#5=#43018,20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38+$23#1$2;+$2<-1#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,2'$2<#2#1?'$23#1#7???????????,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274456 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274492 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274492 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbLm.

Module LibSegNs_tbM0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274480].
Definition STOPS1 : list Z := [274480] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2?$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#!$2#10,8#!$2#18,8#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43030#43030#5=#43030,20##43030$2$3$4$39$3:$3;$2:$22$2##+$2#10+$2#8#$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,24!$2#,1#!$2#8,8#!$2#10,8#!$2#18,8#!$2-:8,8#9!$2-:0,8#!$2-98,8#!$2-90,8#!$2-88,8#1!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#7,$2#20#50%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbM0.

Module LibSegNs_tbM1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274480].
Definition STOPS1 : list Z := [274480] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2?$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#1!$2#10,8$24!$2#18,8#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43030#43030#5;#43860,20##431>4+$2-30$3$4$39$3:$3;$2#:$2##2+$2#10+$2#18+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20#&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20+$2#10##1#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,25!$2#18,8+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20!$2#10,8+@#:00000000&6$24#20@#:&6@#100000000$24#20!$2#8,8#2!$2-:8,8#9!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition s3 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#43860,20##431>4+$2-30$3$4$39$3:$3;$2#:$2##1+$2#10+$2#10+@#:00000000&6$24#20@#:&6@#100000000$24#20#&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20+$2#10##1#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,26!$2#8,8#1'&4&1+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20##1#1#1!$2#18,8+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20!$2#10,8+@#:00000000&6$24#20@#:&6@#100000000$24#20!$2-:8,8#9!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43030#43030#5=#43030,20##43030$2$3$4$39$3:$3;$2:$22$2##+$2#10+$2#8+@#:00000000&6$24#20@#:&6@#100000000$24#20#&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,27!$2#,1#!$2#8,8#'&4&1+@#:00000000&6$24#20@#:&6@#100000000$24#20##1#1#1'&4&1+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20##1#1#1!$2#18,8+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20!$2#10,8+@#:00000000&6$24#20@#:&6@#100000000$24#20!$2-:8,8#9!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#7,$2#20#50%#10000#<6<<0'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43030#43030#5=#43030,20##43030$2$3$4$39$3:$3;$2:$22$2##1+$2#10+$2#10+@#:00000000&6$24#20@#:&6@#100000000$24#20#&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,27'&4&1+@#:00000000&6$24#20@#:&6@#100000000$24#20##1##!$2#8,8#1'&4&1+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20##1#1#1!$2#18,8+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20!$2#10,8+@#:00000000&6$24#20@#:&6@#100000000$24#20!$2-:8,8#9!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43030#43030#5=#43030,20##43030$2$3$4$39$3:$3;$2:$22$2##2+$2#10+$2#18+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20#&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20$23$2;$2<#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,26'&4&1+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20##1##!$2#18,8+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20&6@#:&6$24#20#20!$2#10,8+@#:00000000&6$24#20@#:&6@#100000000$24#20!$2#8,8#2!$2-:8,8#9!$2-:0,8#1!$2-98,8$24!$2-90,8#1!$2-88,8#2!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##8,$2#20#50%#10000#<6<<0!$2#,1#'$24#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 274480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 274480 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s5).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s5).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s5 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s5 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s5).
Definition ps2 : SR.post_spec := SR.PS 274480 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbM1.

End BndP_Ns_071.
Module BndP_Ns_072.
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
Ltac2 kr_t_BndP_Ns_072 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Ns_000ASegItab_Ns_4f613e2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0140:Ns0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbM2g3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMr3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbMt3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbTD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbTI03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI222BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI223NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI222BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI225XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI222F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI223PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI224planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI225regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072?LibSegNs_tbTI223kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbW03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072=LibSegNs_tbWm3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWm13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWph3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbWpl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0n3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0162;BndP_Ns_072>LibSegNs_tbX0p3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNs_tbM2g.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [275516].
Definition STOPS1 : list Z := [275516] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2?$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4343<#4343<#5=#4343<,20##43164+$2-30$3$4$39$3:$3;$2#:$2#3$33$34$35$36$37$38+$2#10$24#2#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,19!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#160,$2##70%#10000#<6<<0!$2#,1#!$2#8,8#2!$2#10,8$24!$2#18,8$26'$24#^#?#???????????????'$26#1^#?#???????????????'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbM2g.

Module LibSegNs_tbMD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [761592].
Definition STOPS1 : list Z := [761592] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$39$3:$3;$2:$22$31$32$33$34$35$36$37$38$23$2;$2<#9$2?$17$18$19$1:$1;$3<$3=$3>$3?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#2!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1)$29##40$23##1'$2:##800000000000'$2;##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 274456 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#;9>?8#;9>?8#5=#;9>?8,20##43164+$2-30$3$4$39$3:$3;$2#:+$29#10##8$34$35$36$37$38+$2#10$24#2#9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,2>!$2#8,8#3!$2-:8,8#9!$2-:0,8#2!$2-98,8$24!$2-90,8#2!$2-88,8#3!$2-80,8$2!$2-78,8#43460!$2-50,8+$2#10!$2-48,8#:!$2-40,8$2!$2-38,8#43164!$2-30,8$2<!$2-28,8$2;!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43030'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##8,$2#10#60%#10000#<6<<0!$2#,1#1!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26,$29#10#30'$24#^#?#???????????????'$26#1^#4#'$23#1#7???????????!$23#,1$2='$2=#30#39)$2-190#200$23##1)$29##40$23##1'$2:##800000000000'$2;##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274456 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274456 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbMD.

Module LibSegNs_tbMr.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274480].
Definition STOPS1 : list Z := [274480] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##431>4+$2-30$3$4$5$6$7$2#:$2$33$34$35$36$37$38$39$29$32#2#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#?#???????????????!$2-8,8#43030!$2-10,8$2:!$2-18,8$22!$2-20,8$23!$2-28,8$2;!$2-30,8$2<'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39"%pstring).
Definition ss0 : sym_state := SS 276524 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43030#43030#5=#43030,20##43030$2$3$4$5$6$7$2:$22$2#1#2$29+$29#8$26$38$39$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$2#8,8#2'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#198,$2#10#60%#10000#<6<<0!$2#,1#1!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#?#???????????????!$2-8,8#43030!$2-10,8$2:!$2-18,8$22!$2-20,8$23!$2-28,8$2;!$2-30,8$2<'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274480 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 276524 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 276524 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbMr.

Module LibSegNs_tbMt.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [276524].
Definition STOPS1 : list Z := [276524] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30+$2-30$3$4$5$6$7$2#:$31$33$34$35$36$37$38$39$32$24#2#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40!$29#,8$24!$29#8,8$26!$29#10,8#,$29#18#28'$24#^#?#???????????????'$26#1^#4#!$2-8,8#43030!$2-10,8$2:!$2-18,8$22!$2-20,8$23!$2-28,8$2;!$2-30,8$2<'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39"%pstring).
Definition ss0 : sym_state := SS 274788 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 432); ((EVar 41), (0), ELit 64)].
Definition F0L : list SR.region := [((EVar 2), (-400), 432); ((EVar 41), (0), 64)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#4382<#4382<#5=#4382<,20##431>4+$2-30$3$4$5$6$7$2#:$2+&4+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20+@#:00000000&6$26#20+&6@#:&6$24#20#20@#:&6@#100000000$26#20+@#:00000000&6$26#20@#:&6@#100000000$26#20+&4+@#:00000000&6$26#20@#:&6@#100000000$26#20@#:00000000&6$26#20&6@#:&6$26#20#20+$29#18#:+$29#18+&4+@#:00000000&6$26#20@#:&6@#100000000$26#20@#:00000000&6$26#20&6@#:&6$26#20#20&4+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20+@#:00000000&6$26#20+&6@#:&6$24#20#20@#:&6@#100000000$26#20+@#:00000000&6$26#20@#:&6@#100000000$26#20&4+@#:00000000&6$26#20@#:&6@#100000000$26#20@#:00000000&6$26#20$29##2#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,1<!$29#10,8+&4+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20+@#:00000000&6$26#20+&6@#:&6$24#20#20@#:&6@#100000000$26#20+@#:00000000&6$26#20@#:&6@#100000000$26#20+&4+@#:00000000&6$26#20@#:&6@#100000000$26#20@#:00000000&6$26#20&6@#:&6$26#20#20!$29#8,8+&4+@#:00000000&6$24#20@#:&6@#100000000$24#20@#:00000000&6$24#20+@#:00000000&6$26#20+&6@#:&6$24#20#20@#:&6@#100000000$26#20!$29#,8+@#:00000000&6$24#20@#:&6@#100000000$24#20'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200!$2#,1#1!$2#8,8#3!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000&$29#10($29##40)$2-190#200$29##40,$29#18#28'$24#^#?#???????????????'$26#1^#4#!$2-8,8#43030!$2-10,8$2:!$2-18,8$22!$2-20,8$23!$2-28,8$2;!$2-30,8$2<'$2:##800000000000'$2;##1'$2<#1#1?'$2=#30#39,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274788 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274788 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbMt.

Module LibSegNs_tbTD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [409028].
Definition STOPS1 : list Z := [409028] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$30$2$3$4$5$6$7$2:$2>$31$32$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1$25'$25##??'&9$25#1#1#1!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000'$2>##16"%pstring).
Definition ss0 : sym_state := SS 274536 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#63=<4#63=<4#5=#63=<4,20##43088$2$3$4$5$6$7$2:$2>$29#40$33$34$35$36$37$38$23$2;$2<#9$2=$17$18$19$1:$1;$1<$1=$1>$1?,,<'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1$25'$25##??'&9$25#1#1#1!$2#10,8#8!$2#18,8$29'$29#1000#7??????00000'$2>##16,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274536 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274536 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbTD.

Module LibSegNs_tbTI0.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1$25'$25##??'&9$25#1##!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16"%pstring).
Definition ss0 : sym_state := SS 274536 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9$2:#$33$34$35$36$37$38$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1$25'$25##??'&9$25#1##!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274536 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274536 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbTI0.

Module LibSegNs_tbTI22.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1$25'$25##??'&9$25#1##!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16"%pstring).
Definition ss0 : sym_state := SS 274536 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9$2:#16$33$34$35$36$37$38$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1$25'$25##??'&9$25#1##!$2#68,8$28!$2#58,8#423<0!$2#50,8$8!$2#48,8$9!$2#40,8$12!$2#38,8$13!$2#30,8$14!$2#28,8$15!$2#20,8$16,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 274536 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 274536 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbTI22.

Module LibSegNs_tbW0.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28+$2#70$3$4$5$6$7$8$9$23#$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 271236 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9$23#16$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271236 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 271236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbW0.

Module LibSegNs_tbWm.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274292].
Definition STOPS1 : list Z := [274292] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28+$2#70$3$4$5$6$7$8$9$23$2<$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#2=#2=)$2-190#200$23##1'$2<#2#1?"%pstring).
Definition ss0 : sym_state := SS 271236 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 512)].
Definition F0L : list SR.region := [((EVar 2), (-400), 512)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42?74#42?74#5=#42?74,20##423<0$2$3$4$5$6$7+$23$2<$22+$23#1#30#1$22+$2#67$?$10$11+$23#1#1+$2<-1$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2#20,8$16!$2#28,8$15!$2#30,8$14!$2#38,8$13!$2#40,8$12!$2#48,8$9!$2#50,8$8!$2#58,8#423<0!$2#68,8$28'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#1;0,$2#60#8%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#2=#2=)$2-190#200$23##1'$2<#2#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274292 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271236 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 271236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbWm.

Module LibSegNs_tbWm1.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28+$2#70$3$4$5$6$7$8$9$23#1$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#2=#2=)$2-190#200$23##1"%pstring).
Definition ss0 : sym_state := SS 271236 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 512)].
Definition F0L : list SR.region := [((EVar 2), (-400), 512)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#423=0#423=0#5=#423=0,20#$28+$2#70$3$4$5$6$7$8$9+$23#1#16#1$22+$2#67$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,13!$2#20,8$16!$2#28,8$15!$2#30,8$14!$2#38,8$13!$2#40,8$12!$2#48,8$9!$2#50,8$8!$2#58,8#423<0!$2#68,8$28'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#1;0,$2#60#8%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#2=#2=)$2-190#200$23##1,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271236 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 271236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbWm1.

Module LibSegNs_tbWph.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274292].
Definition STOPS1 : list Z := [274292] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28+$2#70$3$4$5$6$7$8$9$23$2<$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#2>#??)$2-190#200$23##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 271236 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 512)].
Definition F0L : list SR.region := [((EVar 2), (-400), 512)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42?74#42?74#5=#42?74,20##423<0$2$3$4$5$6$7+$23$2<$22$23#30#$22+$2#66$?$10$11$23#$2<$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2#20,8$16!$2#28,8$15!$2#30,8$14!$2#38,8$13!$2#40,8$12!$2#48,8$9!$2#50,8$8!$2#58,8#423<0!$2#68,8$28'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#1;0,$2#60#8%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=#2>#??)$2-190#200$23##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274292 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271236 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 271236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbWph.

Module LibSegNs_tbWpl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Ns_000.SegItab_Ns_4f613e.ITR.
Definition IT : itab := BndT_Ns_000.SegItab_Ns_4f613e.IT.
Definition ENDS : list Z := [274292].
Definition STOPS1 : list Z := [274292] ++ ENDS.
Definition NX0 : nat := 64.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$28+$2#70$3$4$5$6$7$8$9$23$2<$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=##2<)$2-190#200$23##1'$2<#1#1?"%pstring).
Definition ss0 : sym_state := SS 271236 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-400), ELit 512)].
Definition F0L : list SR.region := [((EVar 2), (-400), 512)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#42?74#42?74#5=#42?74,20##423<0$2$3$4$5$6$7+$23$2<$22$23#30#$22+$2#66$?$10$11$23#$2<$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2#20,8$16!$2#28,8$15!$2#30,8$14!$2#38,8$13!$2#40,8$12!$2#48,8$9!$2#50,8$8!$2#58,8#423<0!$2#68,8$28'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#1;0,$2#60#8%#10000#<6<<0'$23#1#7???????????!$23#,1$2='$2=##2<)$2-190#200$23##1'$2<#1#1?,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 274292 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Ns_000.SegItab_Ns_4f613e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 271236 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := src0_plan_sound_it BndT_Ns_000.SegItab_Ns_4f613e.IT BndT_Ns_000.SegItab_Ns_4f613e.IT_sound BF NX0 BR XSTEP F0 PSS plan 271236 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNs_tbWpl.

Module LibSegNs_tbX0n.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#!$2#10,8#!$2#18,8#'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43068#43068#5=#43068,20##43064$2$3$4$39$3:$3;$2:#$22##2$34$35$36$37$38$23#1##9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,25!$22#8,8#!$2-:8,8#9!$2-:0,8#2!$2-98,8$2!$2-90,8#!$2-88,8#!$2-80,8$22!$2-78,8#43460!$2-50,8#!$2-48,8#!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#1!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064!$2#,1#2'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2#1#6?%#10000#<6<<0!$2#8,8#!$2#10,8#!$2#18,8#'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#10,8#!$22#18,8#,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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
End LibSegNs_tbX0n.

Module LibSegNs_tbX0p.
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
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#200%#10000#<6<<0!$2#,1#!$2#8,8#!$2#10,8#!$2#18,8#'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#8,8#!$22#10,8#!$22#18,8#"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#43068#43068#5=#43068,20##43064$2$3$4$39$3:$3;$2:#$22##2$34$35$36$37$38$23###9$2=$17$18$19$1:$1;$3<$3=$3>$3?,,25!$22#8,8#!$2-:8,8#9!$2-:0,8#!$2-98,8$2!$2-90,8#!$2-88,8#!$2-80,8$22!$2-78,8#43460!$2-50,8#!$2-48,8#!$2-40,8$22!$2-38,8#433=0!$2-30,8#!$2-28,8#!$2-20,8$23!$2-18,8$22!$2-10,8$2:!$2-8,8#43064'$2#7???7?800400#7?????????70&$2#10($2-190#200,$2-190#>8,$2-70#20,$2##70%#10000#<6<<0!$2#,1#!$2#8,8#!$2#10,8#!$2#18,8#'$22#7???7?800000#7?????????>0&$22#8)$2-190#200$22##20'&4&1$22$2#1##($22##20!$22#,1#!$22#10,8#!$22#18,8#,40!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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
End LibSegNs_tbX0p.

End BndP_Ns_072.
