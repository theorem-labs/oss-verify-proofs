(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_002 BndT_Na_001 BndT_Na_003. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_074.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_002 BndT_Na_001 BndT_Na_003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_074 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_1c89a22ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT02BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT05XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT03kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qlpT13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qlpX3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_8edc8b2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrRD3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_7b1e462ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrcI3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_d214862ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdBs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCl3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdCs3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074=LibSegNa_qrdE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_074>LibSegNa_qrdFl3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qlpT0.
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
Definition ss0 : sym_state := SS 852520 regs0 [] kn0 NX0.
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852520 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852520 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpT0.

Module LibSegNa_qlpT1.
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
Definition ss0 : sym_state := SS 852520 regs0 [] kn0 NX0.
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 852520 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 852520 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpT1.

Module LibSegNa_qlpX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_1c89a2.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_1c89a2.IT.
Definition ENDS : list Z := [852776].
Definition STOPS1 : list Z := [852776] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$34+$2->0$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:+&6$32#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?8010>0#800000000000&$2#20!$2-;0,8$32!$2-:8,8$32)+$2->0##>0$32##80'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##8(&6$32#3#7???8000#10!$32#78,8$33'$33#1000#7???????????($33##1)##7???7000#100000001000$33##1)$32##80$33##1'$34#7???7?8010>0#800000000000&$34#10!$34-8,8$3<!$34-10,8$3=!$34-18,8$3>!$34-20,8$3?!$34-28,8$40!$34-30,8$41!$34-38,8$42!$34-40,8$43!$34-48,8$44!$34-50,8$45!$34-58,8$46!$34-60,8$47!$34-68,8$48)+$34->0##>0$32##80)+$34->0##>0$33##1"%pstring).
Definition ss0 : sym_state := SS 851692 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 50), (0), ELit 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 16); ((EVar 51), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 50), (0), 8); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 16); ((EVar 51), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=0328#=0328#5=#=0328,20#$3<$34$3$4$5$6$7$3=$3>$33$32$<$=$>$?$10$11$3?$40$41$42$43$44$45$46$47$48$1<$1=$1>$1?,,30!$33#,1#!&6$32#3#7???800;,1^#?#??????????????5!&6$32#3#7???800:,1^#?#??????????????5!&6$32#3#7???8009,1^#?#??????????????5!&6$32#3#7???8008,1^#?#??????????????5!&6$32#3#7???800?,1^#?#??????????????5!&6$32#3#7???800>,1^#?#??????????????5!&6$32#3#7???800=,1^#?#??????????????5!&6$32#3#7???800<,1^#?#??????????????5!&6$32#3#7???8003,1^#?#??????????????5!&6$32#3#7???8002,1^#?#??????????????5!&6$32#3#7???8001,1^#?#??????????????5!&6$32#3#7???8000,1^#?#??????????????5!&6$32#3#7???8007,1^#?#??????????????5!&6$32#3#7???8006,1^#?#??????????????5!&6$32#3#7???8005,1^#?#??????????????5!&6$32#3#7???8004,1^#?#??????????????5!$32#,8#45>0360>'$2#7???7?8010>0#800000000000&$2#20)+$2->0##>0$32##80'$32#6;6000#7?????????80&$32#20)##7???7000#100000001000$32##80($32##8(&6$32#3#7???8000#10!$32#78,8$33'$33#1000#7???????????($33##1)##7???7000#100000001000$33##1)$32##80$33##1'$34#7???7?8010>0#800000000000&$34#10!$34-8,8$3<!$34-10,8$3=!$34-18,8$3>!$34-20,8$3?!$34-28,8$40!$34-30,8$41!$34-38,8$42!$34-40,8$43!$34-48,8$44!$34-50,8$45!$34-58,8$46!$34-60,8$47!$34-68,8$48)+$34->0##>0$32##80)+$34->0##>0$33##1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 852776 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_1c89a2.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851692 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_1c89a2.IT BndT_Na_000.SegItab_Na_1c89a2.IT_sound BF NX0 BR XSTEP F0 PSS plan 851692 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qlpX.

Module LibSegNa_qrRD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_8edc8b.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_8edc8b.IT.
Definition ENDS : list Z := [828944].
Definition STOPS1 : list Z := [828944; 828948; 828560; 828816; 828996] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801070#800000000000&$2#10($2-70#70'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-70#70$21##20!$21#,1$26'$26##??'&9$26#1#1#1!$21#10,8#8'$22##8"%pstring).
Definition ss0 : sym_state := SS 828448 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-104), ELit 104)].
Definition F0L : list SR.region := [((EVar 2), (-104), 104)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:610#<:614#<:490#<:590#<:644#<:610#5=#<:610,20#$1$2$3$4$5$6$7$8$9#8##15?:78$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801070#800000000000&$2#10($2-70#70'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-70#70$21##20!$21#,1$26'$26##??'&9$26#1#1#1!$21#10,8#8'$22##8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 828944 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_8edc8b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 828448 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_8edc8b.IT BndT_Na_002.SegItab_Na_8edc8b.IT_sound BF NX0 BR XSTEP F0 PSS plan 828448 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrRD.

Module LibSegNa_qrcD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_7b1e46.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_7b1e46.IT.
Definition ENDS : list Z := [836428].
Definition STOPS1 : list Z := [836428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 39); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1>%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-10#10$21##20!$21#,1$26'$26##??'&9$26#1#1#1'&9$26#2##!$21#8,8#2!$21#18,8$24'$24#1000#7?????????<0'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8#1!$27#10,8$25'&9$29#2##)$2-10#10$27##20"%pstring).
Definition ss0 : sym_state := SS 836056 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<<34<#<<34<#5=#<<34<,20#$1$2$3$4$5$6$7$8$9#1#1$24#7???8000##2+$27#10#$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1?!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-10#10$21##20!$21#,1$26'$26##??'&9$26#1#1#1'&9$26#2##!$21#8,8#2!$21#18,8$24'$24#1000#7?????????<0'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8#1!$27#10,8$25'&9$29#2##)$2-10#10$27##20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 836428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_7b1e46.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 836056 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_7b1e46.IT BndT_Na_001.SegItab_Na_7b1e46.IT_sound BF NX0 BR XSTEP F0 PSS plan 836056 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrcD.

Module LibSegNa_qrcI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_7b1e46.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_7b1e46.IT.
Definition ENDS : list Z := [836428].
Definition STOPS1 : list Z := [836428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 39); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-10#10$21##20!$21#,1$26'$26##??'&9$26#1##'&9$26#2##!$21#8,8#2'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8#1!$27#10,8$25'&9$29#2##)$2-10#10$27##20"%pstring).
Definition ss0 : sym_state := SS 836056 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-8), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-8), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<<34<#<<34<#5=#<<34<,20#$1$2$3$4$5$6$7$8$9#1#1+$21#10#7???8000##2+$27#10#$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801010#800000000000&$2#10($2-10#10'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-10#10$21##20!$21#,1$26'$26##??'&9$26#1##'&9$26#2##!$21#8,8#2'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8#1!$27#10,8$25'&9$29#2##)$2-10#10$27##20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 836428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_7b1e46.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 836056 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_7b1e46.IT BndT_Na_001.SegItab_Na_7b1e46.IT_sound BF NX0 BR XSTEP F0 PSS plan 836056 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrcI.

Module LibSegNa_qrdA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [754280].
Definition STOPS1 : list Z := [754280; 720804] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?801020#800000000000&$2#10($2-20#20%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#190#3#7???8000#1($21#190#8"%pstring).
Definition ss0 : sym_state := SS 720724 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((EVar 33), (400), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((EVar 33), (400), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;8268#:??:4#;8268#5=#;8268,20##:??:4+$2-20$3$4$5$6$7$21#7???8000+$2-20#$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,11!$2-20,8+$21#1=8!$21#190,8#150=88!$2-18,8$9!$2-10,8$8!$2-8,8$1'$2#7???7?801020#800000000000&$2#10($2-20#20%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#190#3#7???8000#1($21#190#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 754280 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720724 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 720724 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdA.

Module LibSegNa_qrdBl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168; 720880] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1<0#3#7???8000#3!$21#1<0,1$23'$23##??'&9$23#1#1#1,$21#1<1#7!$21#1=0,8$24'$24#1000#800000000000#&6+$21#1=0#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 720804 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?1?<0#:???0#?1?<0#5=#?1?<0,20##:???0+$2-20$3$4$5$6$7$21#7???8000$24@#2&6$50#1$50#$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1<0#3#7???8000#3!$21#1<0,1$23'$23##??'&9$23#1#1#1,$21#1<1#7!$21#1=0,8$24'$24#1000#800000000000#&6+$21#1=0#3#7???8000#1,51!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720804 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 720804 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdBl.

Module LibSegNa_qrdBs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [720880].
Definition STOPS1 : list Z := [720880; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1<0#3#7???8000#3!$21#1<0,1$23'$23##??'&9$23#1##"%pstring).
Definition ss0 : sym_state := SS 720804 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#:???0#?1?<0#:???0#5=#:???0,20#$1+$2-20$3$4$5$6$7$21#7???8000+$21#1<0#+&6+$21#1<0#3#7???8000$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1<0#3#7???8000#3!$21#1<0,1$23'$23##??'&9$23#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 720880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720804 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 720804 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdBs.

Module LibSegNa_qrdCl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168; 720956] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1:8#3#7???8000#3!$21#1:8,1$25'$25##??'&9$25#1#1#1,$21#1:9#7!$21#1;8,8$26'$26#1000#800000000000#&6+$21#1;8#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 720880 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?1?<0#;003<#?1?<0#5=#?1?<0,20##;003<+$2-20$3$4$5$6$7$21#7???8000$26@#2&6$50#1$50#$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1:8#3#7???8000#3!$21#1:8,1$25'$25##??'&9$25#1#1#1,$21#1:9#7!$21#1;8,8$26'$26#1000#800000000000#&6+$21#1;8#3#7???8000#1,51!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720880 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 720880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdCl.

Module LibSegNa_qrdCs.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [720956].
Definition STOPS1 : list Z := [720956; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1:8#3#7???8000#3!$21#1:8,1$25'$25##??'&9$25#1##"%pstring).
Definition ss0 : sym_state := SS 720880 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#;003<#?1?<0#;003<#5=#;003<,20#$1+$2-20$3$4$5$6$7$21#7???8000+$21#1:8#+&6+$21#1:8#3#7???8000$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#1:8#3#7???8000#3!$21#1:8,1$25'$25##??'&9$25#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 720956 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720880 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 720880 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdCs.

Module LibSegNa_qrdD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [789880].
Definition STOPS1 : list Z := [789880; 721000] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?801020#800000000000&$2#10%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6$21#3#7???8000#1($21##8($2-20#8"%pstring).
Definition ss0 : sym_state := SS 720956 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 8); ((EVar 33), (0), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-32), 8); ((EVar 33), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<0=78#;0068#<0=78#5=#<0=78,20##;0068+$2-20$3$4$5$6$7$21#7???8000+$2-20$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>!$2-20,8+$21#178!$21#,8#150?>8'$2#7???7?801020#800000000000&$2#10%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6$21#3#7???8000#1($21##8($2-20#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 789880 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720956 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 720956 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdD.

Module LibSegNa_qrdE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [791440].
Definition STOPS1 : list Z := [791440; 721016] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487200 140737488355328;
   KAlign (EVar 2) 16;
   KRange (EVar 33) 7036928 140737488354824;
   KWr (SA (EVar 2) (-32)) (ELit 8)].
Definition ss0 : sym_state := SS 721000 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-32), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<1390#;0078#<1390#5=#<1390,20##;0078+$2-20$3$4$5$6$7$21#7???8000+$2-20$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5!$2-20,8+$21#160'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08($2-20#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 791440 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 721000 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 721000 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdE.

Module LibSegNa_qrdFl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_d21486.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_d21486.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [991168; 721092] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-20$3$4$5$6$7$21#7???8000$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#148#3#7???8000#3!$21#148,1$27'$27##??'&9$27#1#1#1,$21#149#7!$21#158,8$28'$28#1000#800000000000#&6+$21#158#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 721016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#?1?<0#;00<4#?1?<0#5=#?1?<0,20##;00<4+$2-20$3$4$5$6$7$21#7???8000$28@#2&6$50#1$50#$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,>'$2#7???7?801020#800000000000&$2#10'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8)$2-20#20$21##1?8#&6+$21#148#3#7???8000#3!$21#148,1$27'$27##??'&9$27#1#1#1,$21#149#7!$21#158,8$28'$28#1000#800000000000#&6+$21#158#3#7???8000#1,51!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_d21486.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 721016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_d21486.IT BndT_Na_003.SegItab_Na_d21486.IT_sound BF NX0 BR XSTEP F0 PSS plan 721016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrdFl.

End BndP_Na_074.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_003 BndT_Na_001 BndT_Na_000.
Module BndP_Na_094.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_003 BndT_Na_001 BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_094 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_eab0ed2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12a3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094ALibSegNa_qriZE12b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE82BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE83NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE82BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE85XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE82F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE83PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE84planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE85regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZE83kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZRF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZS23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZSW3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094?LibSegNa_qriZXe3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_67b7792ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrmA3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_25fae12ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnA3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrnC3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_62297b2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_094=LibSegNa_qrq03kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qriZE12a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 859764 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",4$21#8#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",4$21#8#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,10!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???8044,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859764 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859764 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZE12a.

Module LibSegNa_qriZE12b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 860176 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",5$21#8#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#46#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",5$21#8#1+&6$32#3#7???8000#44#1+&6$32#3#7???8000#46#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,11!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???8046,1^#?#??????????????8!&6$32#3#7???8044,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860176 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZE12b.

Module LibSegNa_qriZE4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 859104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",4$21#8#1+&6$32#3#7???8000#32#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",4$21#8#1+&6$32#3#7???8000#32#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8#$<#$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,10!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???8032,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZE4.

Module LibSegNa_qriZE8.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 859720 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionP) ",4$21#8#1+&6$32#3#7???8000#34#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition F0L : list SR.region := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_regionR) ",4$21#8#1+&6$32#3#7???8000#34#1+&6$32#3#7???8000#30#1+&6$32#3#7???8000#<#1"%pstring).
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,10!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!&6$32#3#7???8034,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 859720 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 859720 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZE8.

Module LibSegNa_qriZRF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 860740 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (48), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (48), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8#$<#$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,?!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 860740 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 860740 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZRF.

Module LibSegNa_qriZS2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$21#8$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-88,8+&6+$21#8#3#7???8000"%pstring).
Definition ss0 : sym_state := SS 858360 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8#$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16+$21#8$18$19#7???8000$1;$1<$1=$1>$1?,,>!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 858360 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 858360 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZS2.

Module LibSegNa_qriZSF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855320 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8#$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,<!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZSF.

Module LibSegNa_qriZSW.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80"%pstring).
Definition ss0 : sym_state := SS 855032 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8$9^#?#??????????????8#$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,<!&6$32#3#7???800<,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855032 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855032 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZSW.

Module LibSegNa_qriZXe.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_eab0ed.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_eab0ed.IT.
Definition ENDS : list Z := [854444].
Definition STOPS1 : list Z := [854444] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-:0$3$4$5$6$7$8+$2-:0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20!$2-90,8+&6+$21#8#3#7???8000!$2-88,8+$21#8"%pstring).
Definition ss0 : sym_state := SS 855472 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (8), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (48), ELit 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (8), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (48), 1); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#=09:<#=09:<#5=#=09:<,20#$1+$2-:0$3$4$5$6$7$8+$2-:0^#?#??????????????8$;$<$=$>$?$10$11$12+&6$32#3#7???8000$21$15$16$17$18$19#7???8000$1;$1<$1=$1>$1?,,?!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8030,1^#?#??????????????8!$21#8,1#'$21#6;6000#7????????>08&$21#8)##7???7000#100000001000$21##1?8#&6+$21#8#3#7???8000#1($21#8#1'$32#6;6000#7????????<00&$32#20)##7???7000#100000001000$32##400(&6$32#3#7???8000#80)&6+$21#8#3#7???8000#2&6$32#3#7???8000#80'$2#7???7?8010:0#800000000000&$2#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 854444 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_eab0ed.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 855472 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_eab0ed.IT BndT_Na_003.SegItab_Na_eab0ed.IT_sound BF NX0 BR XSTEP F0 PSS plan 855472 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qriZXe.

Module LibSegNa_qrmA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_67b779.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_67b779.IT.
Definition ENDS : list Z := [837660; 837856].
Definition STOPS1 : list Z := [837660; 837856] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$22+$21#10+$27#10#1$25$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-50#50$21##20!$21#10,8$23!$21#18,8$24'$23#^#?#???????????????'$24#1#40000000'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8$28!$27#10,8^#8#:<7230489>80000)$21##20$27##20)$2-50#50$27##20'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1!$25#,8$2:'$2:#1#7???????)$2-50#50$25##8)$21##20$25##8)$27##20$25##8"%pstring).
Definition ss0 : sym_state := SS 837320 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 33), (16), ELit 16)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 33), (16), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<<81<#<<8>0#<<81<#<<8>0#5;#<<818,20#$1+$2-50$3$4+$21#20#????????+&6$25#3#7???8000+$24+@-1&4$23@^-7-538=<?;76180000$2:+@-1&4@^-7-538=<?;76180000$2:@#89>80000$2:@-1&6@#8:<72304$2:#20+$21#18+$27#18+$21#10+$27#10#1$25+$21#18#7???8000+&6+$21#10#3#7???8000$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20@^-7-538=<?;76180000$2:&6@#8:<72304$2:#20###$19$1:$1;+&6+$27#10#3#7???8001+$27#18#&4$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20,,2>!$21#18,8+$24+@-1&4$23@^-7-538=<?;76180000$2:+@-1&4@^-7-538=<?;76180000$2:@#89>80000$2:@-1&6@#8:<72304$2:#20!$21#10,8+$23@^#7#538=<?;76180000$2:!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-50#50$21##20'$23#^#?#???????????????'$24#1#40000000'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8$28!$27#10,8^#8#:<7230489>80000)$21##20$27##20)$2-50#50$27##20'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1!$25#,8$2:'$2:#1#7???????)$2-50#50$25##8)$21##20$25##8)$27##20$25##8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<<81<#<<8>0#<<81<#<<8>0#5=#<<81<,20#$1+$2-50$3$4+$21#20#????????+&6$25#3#7???8000+$24+@-1&4$23@^-7-538=<?;76180000$2:+@-1&4@^-7-538=<?;76180000$2:@#89>80000$2:@-1&6@#8:<72304$2:#20+$21#18+$27#18+$21#10+$27#10#1$25+$21#18#7???8000+&6+$21#10#3#7???8000$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20@^-7-538=<?;76180000$2:&6@#8:<72304$2:#20###$19$1:$1;+&6+$27#10#3#7???8001+$27#18#&4$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20,,2?'&4$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20#1#1!$21#18,8+$24+@-1&4$23@^-7-538=<?;76180000$2:+@-1&4@^-7-538=<?;76180000$2:@#89>80000$2:@-1&6@#8:<72304$2:#20!$21#10,8+$23@^#7#538=<?;76180000$2:!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-50#50$21##20'$23#^#?#???????????????'$24#1#40000000'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8$28!$27#10,8^#8#:<7230489>80000)$21##20$27##20)$2-50#50$27##20'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1!$25#,8$2:'$2:#1#7???????)$2-50#50$25##8)$21##20$25##8)$27##20$25##8,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<<81<#<<8>0#<<81<#<<8>0#5=#<<8>0,20#$1$2$3$4+$21#20#????????+&6$25#3#7???8000$8$9+$27#18+$21#10+$27#10#1$25+$21#18#7???8000+&6+$21#10#3#7???8000$12$13$14$15$16$17$18$19$1:$1;+&6+$27#10#3#7???8001+$27#18#&4$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20,,2?'&4$24+&4$23@^-7-538=<?;76180000$2:+&4@^-7-538=<?;76180000$2:@#89>80000$2:&6@#8:<72304$2:#20##!$21#18,8+$24+@-1&4$23@^-7-538=<?;76180000$2:+@-1&4@^-7-538=<?;76180000$2:@#89>80000$2:@-1&6@#8:<72304$2:#20!$21#10,8+$23@^#7#538=<?;76180000$2:!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-50#50$21##20'$23#^#?#???????????????'$24#1#40000000'$27#6;6000#7?????????>0&$27#8)##7???7000#100000001000$27##20#&6$27#3#7???8000#4!$27#,1$29'$29##??'&9$29#1##!$27#8,8$28!$27#10,8^#8#:<7230489>80000)$21##20$27##20)$2-50#50$27##20'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1!$25#,8$2:'$2:#1#7???????)$2-50#50$25##8)$21##20$25##8)$27##20$25##8,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 837660 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 837856 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_67b779.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 837320 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_67b779.IT BndT_Na_001.SegItab_Na_67b779.IT_sound BF NX0 BR XSTEP F0 PSS plan 837320 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrmA.

Module LibSegNa_qrnA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_25fae1.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_25fae1.IT.
Definition ENDS : list Z := [838464].
Definition STOPS1 : list Z := [838464; 839180; 836960] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$22$21$27+$25#4$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1;%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-50#50$21##20!$21#,1$26'$26##??'&9$26#1##!$21#8,8#1!$21#10,8$24'$24^#8#^#?#???????????????'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1#&6+$25#4#3#7???8000#1($25##8)$2-50#50$25##8)$21##20$25##8)$27##20$25##8"%pstring).
Definition ss0 : sym_state := SS 836496 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-80), ELit 80); ((EVar 37), (4), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-80), 80); ((EVar 37), (4), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<<;40#<<>0<#<<560#<<;40#5=#<<;40,20##<<484+$2-50$3$4$5$6$7$21$27$21##+$25#4$>$?$10$11+$25#4#7???8000#1+&6$21#3#7???8000##+&6+$25#4#3#7???8000$19$1:$1;$1<$1=$1>$1?,,26!$25#4,4#!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801050#800000000000&$2#10($2-50#50'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-50#50$21##20!$21#,1$26'$26##??'&9$26#1##!$21#8,8#1!$21#10,8$24'$24^#8#^#?#???????????????'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1#&6+$25#4#3#7???8000#1($25##8)$2-50#50$25##8)$21##20$25##8)$27##20$25##8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 838464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_25fae1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 836496 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_25fae1.IT BndT_Na_000.SegItab_Na_25fae1.IT_sound BF NX0 BR XSTEP F0 PSS plan 836496 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrnA.

Module LibSegNa_qrnB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_25fae1.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_25fae1.IT.
Definition ENDS : list Z := [838464].
Definition STOPS1 : list Z := [838464; 839180; 836960] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$21$27$:$;$<$=$>$?$10$11+$25#4#7???8000#1+&6$21#3#7???8000##+&6+$25#4#3#7???8000$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?801050#800000000000&$2#10'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1#&6+$25#4#3#7???8000#1($25##8)$2-50#50$25##8)$21##20$25##8)$27##20$25##8!$25#4,4#"%pstring).
Definition ss0 : sym_state := SS 836740 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<<;40#<<>0<#<<560#<<;40#5=#<<;40,20##<<498+$2-50$3$4$5$6$7$21$27$27#$<$=$>$?$10$11+$25#4#7???8000#1+&6$21#3#7???8000##+&6+$25#4#3#7???8000$19$1:$1;$1<$1=$1>$1?,,<'$2#7???7?801050#800000000000&$2#10'$25#7???7?801000#7??????????8&$25#8)##7???7000#100000001000$25##8#&6$25#3#7???8000#1#&6+$25#4#3#7???8000#1($25##8)$2-50#50$25##8)$21##20$25##8)$27##20$25##8!$25#4,4#,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 838464 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_25fae1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 836740 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_25fae1.IT BndT_Na_000.SegItab_Na_25fae1.IT_sound BF NX0 BR XSTEP F0 PSS plan 836740 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrnB.

Module LibSegNa_qrnC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_25fae1.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_25fae1.IT.
Definition ENDS : list Z := [836960].
Definition STOPS1 : list Z := [836960; 839180; 838464] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$21$27$:$;$<$=$>$?$10$11$12$13$14+&6$21#3#7???8000$16#$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",14'$2#7???7?801050#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37!$2-20,8$38!$2-28,8$39!$2-30,8$3:!$2-38,8$3;!$2-40,8$3<!$2-48,8$3=!$2-50,8$3>'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##"%pstring).
Definition ss0 : sym_state := SS 836760 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<<560#<<>0<#<<;40#<<560#5=#<<560,20#$35$2$3$4$5$6$7$36$37#+$21#10$<$=$>$?$10$11$38$39$3:$3;$3<$3=$3>$19$1:$1;$1<$1=$1>$1?,,14'$2#7???7?801050#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37!$2-20,8$38!$2-28,8$39!$2-30,8$3:!$2-38,8$3;!$2-40,8$3<!$2-48,8$3=!$2-50,8$3>'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 836960 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_25fae1.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 836760 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_25fae1.IT BndT_Na_000.SegItab_Na_25fae1.IT_sound BF NX0 BR XSTEP F0 PSS plan 836760 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrnC.

Module LibSegNa_qrq0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_62297b.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_62297b.IT.
Definition ENDS : list Z := [837176].
Definition STOPS1 : list Z := [837316] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$:$21$22^#8#:<7230489>80000$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 1 1073741824].
Definition ss0 : sym_state := SS 837064 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<<6<4#<<638#5=#<<638,20#$1$2$3$4^#8#9>8000000000000#????????+$21@-8:<72304/5$21#8:<72305$8$9#$22&4$22#^#8#:<7230489>80000#8:<72304#89>80000#8:<72305+$21+@-1&4$22#@-8:<72304/5$21#8:<72305$12$13$14$15$16$17$18$19$1:$1;#$1=$1>$1?,,1'$21#1#40000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 837176 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_62297b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 837064 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_62297b.IT BndT_Na_001.SegItab_Na_62297b.IT_sound BF NX0 BR XSTEP F0 PSS plan 837064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrq0.

End BndP_Na_094.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_000 BndT_Na_002.
Module BndP_Na_095.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_000 BndT_Na_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_095 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_62297b2ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq12BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq15XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq13kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrq23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_0ecc262ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsA3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_9a423e2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrsAS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsM3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsT3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrsZ3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_44d4102ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095>LibSegNa_qrvEd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvF3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_095=LibSegNa_qrvH3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qrq1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_62297b.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_62297b.IT.
Definition ENDS : list Z := [837280; 837312].
Definition STOPS1 : list Z := [837316] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9#$22$<^#8#:<7230489>80000#8:<72304#89>80000#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 1073741824].
Definition ss0 : sym_state := SS 837176 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5;#<<684,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#$22/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1'$21##40000000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5;#<<688,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#$22/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1#1#1'$21##40000000,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5=#<<6<0,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#$22/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000#1#1'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1#1#1'$21##40000000,50!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5=#<<6:0,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#++$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20#@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000##'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1#1#1'$21##40000000,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5=#<<6:0,20#$1$2$3$4^#8#:<7230489>80000&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305$8$9#++$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20&4+$22@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305^#8#:<7230489>80000@^#7#538=<?;76180000/5&8@#100000000$21&6$22#20#8:<72305$21$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'&4&1+$21+@-1&4$22@#89>80000/5&8@#100000000$21&6$22#20#8:<72305+@-1&4+$22@-89>80000/5&8@#100000000$21&6$22#20#8:<72305@^-7-538=<?<00000000/5&8@#100000000$21&6$22#20#8:<72305@-1&6@#8:<72304/5&8@#100000000$21&6$22#20#8:<72305#20##1##'$21##40000000,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 837312 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 837280 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 837280 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_62297b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 837176 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_62297b.IT BndT_Na_001.SegItab_Na_62297b.IT_sound BF NX0 BR XSTEP F0 PSS plan 837176 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrq1.

Module LibSegNa_qrq2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_62297b.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_62297b.IT.
Definition ENDS : list Z := [837280; 837312].
Definition STOPS1 : list Z := [837316] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9#$23$24^#8#:<7230489>80000$21$22$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 34) 0 1].
Definition ss0 : sym_state := SS 837280 regs0 [] kn0 NX0.
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

Definition s1 : sym_state := Eval vm_compute in (SegCodec.run SegCodec.sc_sstate "#<<6;8,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1$22&4$23^#8#:<7230489>80000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1'$22##1,50!"%pstring).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5;#<<6;<,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1$22&4$23^#8#:<7230489>80000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'&4&1+$21@-1$22##1#1#1'$22##1,50!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5=#<<6<0,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1$22&4$23^#8#:<7230489>80000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4$23^#8#:<7230489>80000#1#1'&4&1+$21@-1$22##1#1#1'$22##1,50!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition ex6 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5=#<<6:0,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1$22&4$23^#8#:<7230489>80000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,3'&4$23^#8#:<7230489>80000##'&4&1+$21@-1$22##1#1#1'$22##1,50!"%pstring).
Definition s6 : sym_state := snd (snd ex6).

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<<6<4#<<6:0#<<6<0#5=#<<6:0,20#$1$2$3$4$5$6$7$8$9#+$23^#7#538=<?;76180000+$24#1^#8#:<7230489>80000+$21@-1$22&4$23^#8#:<7230489>80000$23$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,2'&4&1+$21@-1$22##1##'$22##1,50!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition plan : SGP.splan := SGP.PStep (SR.SBlock STOPS1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PEnd 0)) (SGA.mkplan (fst ex6) (SGP.PEnd 1)))) (SGA.mkplan (fst ex7) (SGP.PEnd 2))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 837312 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SR.PS 837280 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s7).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s7).
Definition ps2 : SR.post_spec := SR.PS 837280 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_62297b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 837280 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_62297b.IT BndT_Na_001.SegItab_Na_62297b.IT_sound BF NX0 BR XSTEP F0 PSS plan 837280 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrq2.

Module LibSegNa_qrsA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0ecc26.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0ecc26.IT.
Definition ENDS : list Z := [830872].
Definition STOPS1 : list Z := [830872; 827428; 839080] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (ELit 0); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-40#40$21##20"%pstring).
Definition ss0 : sym_state := SS 838464 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<:=98#<:024#<<=:8#<:=98#5=#<:=98,20##<<=80+$2-40$3$4$5$6$7$21#$21$50#15?:78$=$>$?$10$11+$21#8#7???8000+&6+$21#8#3#7???8000&6$21#3#$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-40#40$21##20,51!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0ecc26.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 838464 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0ecc26.IT BndT_Na_000.SegItab_Na_0ecc26.IT_sound BF NX0 BR XSTEP F0 PSS plan 838464 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsA.

Module LibSegNa_qrsAL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9a423e.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9a423e.IT.
Definition ENDS : list Z := [791888].
Definition STOPS1 : list Z := [791888; 851104] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",21%#10000#158000!##15?:78,8#7???8000'$2#7???7?801030#800000000000&$2#10($2-20#20'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190)$2-30#30$21##190#&6+$21#8#3#7???8000#1#&6+$21#9#3#7???8000#1#&6+$21#148#3#7???8000#1($21#8#2!$21#148,1$26'$26##??'&9$26#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$27'$27#1000#7??????????8&$27#8)##7???7000#100000001000$27##1#&6$27#3#7???8000#1($27##1)$2-30#30$27##1)$27##1$21##190)##10000#6:6000$27##1($21#150#8#&6+$21#168#3#7???8000#1#&6+$21#160#3#7???8000#1!$21#160,8$28!$21#168,8$29($21#168#8"%pstring).
Definition ss0 : sym_state := SS 850812 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((EVar 33), (8), ELit 2); ((EVar 39), (0), ELit 1); ((EVar 33), (336), ELit 8); ((EVar 33), (360), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((EVar 33), (8), 2); ((EVar 39), (0), 1); ((EVar 33), (336), 8); ((EVar 33), (360), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<1550#<?<:0#<1550#5=#<1550,20##<?<:0+$2-30$3$4$5$6$7$21$9+$21#160+@-1$28$29+$21#160$28$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,29!$21#168,8$28!$21#150,8#!$27#,1#!$21#9,1#!$21#8,1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000'$2#7???7?801030#800000000000&$2#10($2-20#20'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190)$2-30#30$21##190#&6+$21#8#3#7???8000#1#&6+$21#9#3#7???8000#1#&6+$21#148#3#7???8000#1($21#8#2!$21#148,1$26'$26##??'&9$26#1#1#1#&6+$21#158#3#7???8000#1#&6+$21#150#3#7???8000#1!$21#158,8$27'$27#1000#7??????????8&$27#8)##7???7000#100000001000$27##1#&6$27#3#7???8000#1($27##1)$2-30#30$27##1)$27##1$21##190)##10000#6:6000$27##1($21#150#8#&6+$21#168#3#7???8000#1#&6+$21#160#3#7???8000#1!$21#160,8$28($21#168#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 791888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9a423e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 850812 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9a423e.IT BndT_Na_002.SegItab_Na_9a423e.IT_sound BF NX0 BR XSTEP F0 PSS plan 850812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsAL.

Module LibSegNa_qrsAS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9a423e.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9a423e.IT.
Definition ENDS : list Z := [791888].
Definition STOPS1 : list Z := [791888; 851104] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17%#10000#158000!##15?:78,8#7???8000'$2#7???7?801030#800000000000&$2#10($2-20#20'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190)$2-30#30$21##190#&6+$21#8#3#7???8000#1#&6+$21#9#3#7???8000#1#&6+$21#148#3#7???8000#1($21#8#2!$21#148,1$26'$26##??'&9$26#1###&6+$21#149#3#7???8000#1($21#148#2#&6+$21#168#3#7???8000#1#&6+$21#160#3#7???8000#1!$21#160,8$28!$21#168,8$29($21#168#8"%pstring).
Definition ss0 : sym_state := SS 850812 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-32), ELit 32); ((EVar 33), (8), ELit 2); ((EVar 33), (328), ELit 2); ((EVar 33), (360), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-32), 32); ((EVar 33), (8), 2); ((EVar 33), (328), 2); ((EVar 33), (360), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<1550#<?<:0#<1550#5=#<1550,20##<?<:0+$2-30$3$4$5$6$7$21$9+$21#160+@-1$28$29+$21#160$28$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1>!$21#168,8$28!$21#148,1#!$21#149,1#!$21#9,1#!$21#8,1#1!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000'$2#7???7?801030#800000000000&$2#10($2-20#20'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190)$2-30#30$21##190#&6+$21#8#3#7???8000#1#&6+$21#9#3#7???8000#1#&6+$21#148#3#7???8000#1($21#8#2'$26##??'&9$26#1###&6+$21#149#3#7???8000#1($21#148#2#&6+$21#168#3#7???8000#1#&6+$21#160#3#7???8000#1!$21#160,8$28($21#168#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 791888 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9a423e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 850812 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9a423e.IT BndT_Na_002.SegItab_Na_9a423e.IT_sound BF NX0 BR XSTEP F0 PSS plan 850812 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsAS.

Module LibSegNa_qrsB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_0ecc26.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_0ecc26.IT.
Definition ENDS : list Z := [839080].
Definition STOPS1 : list Z := [839080] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$21$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801040#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37!$2-20,8$38!$2-28,8$39!$2-30,8$3:!$2-38,8$3;!$2-40,8$3<"%pstring).
Definition ss0 : sym_state := SS 839040 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<<=:8#<<=:8#5=#<<=:8,20#$35$2$3$4$5$6$7$36$37$21$;$<$=$>$?$10$11$38$39$3:$3;$3<$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?801040#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37!$2-20,8$38!$2-28,8$39!$2-30,8$3:!$2-38,8$3;!$2-40,8$3<,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 839080 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_0ecc26.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 839040 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_0ecc26.IT BndT_Na_000.SegItab_Na_0ecc26.IT_sound BF NX0 BR XSTEP F0 PSS plan 839040 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsB.

Module LibSegNa_qrsM.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9a423e.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9a423e.IT.
Definition ENDS : list Z := [848248].
Definition STOPS1 : list Z := [848248; 851208] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$8+$21#178$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332487216 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-40)) (ELit 8)].
Definition ss0 : sym_state := SS 851184 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-40), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-40), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<?178#<?=08#<?178#5=#<?178,20##<?=08+$2-30$3$4$5$6$7$8+$21#178+$21#178+$2-24+$2-28$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,5!$2-28,4#!$2-24,4#'$2#7???7?801030#800000000000&$2#10($2-28#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 848248 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9a423e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851184 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9a423e.IT BndT_Na_002.SegItab_Na_9a423e.IT_sound BF NX0 BR XSTEP F0 PSS plan 851184 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsM.

Module LibSegNa_qrsT.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9a423e.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9a423e.IT.
Definition ENDS : list Z := [790344].
Definition STOPS1 : list Z := [790344; 851184] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$21$9$:$;$<$=$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9%#10000#158000'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190#&6+$21#180#3#7???8000#1#&6+$21#178#3#7???8000#1!$21#178,8$2:!$21#180,8$2;($21#180#8"%pstring).
Definition ss0 : sym_state := SS 851104 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#<0?48#<?<?0#<0?48#5=#<0?48,20##<?<?0+$2-30$3$4$5$6$7$21+$21#178+$21#178@^-5-555555555555555&7+@-1$2:$2;#3$2:$=$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,9!$21#180,8$2:%#10000#158000'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190#&6+$21#180#3#7???8000#1#&6+$21#178#3#7???8000#1!$21#178,8$2:($21#180#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9a423e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851104 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9a423e.IT BndT_Na_002.SegItab_Na_9a423e.IT_sound BF NX0 BR XSTEP F0 PSS plan 851104 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsT.

Module LibSegNa_qrsZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_9a423e.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_9a423e.IT.
Definition ENDS : list Z := [851252].
Definition STOPS1 : list Z := [851252] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-30$3$4$5$6$7$21$9$:$;$<$=$>$?$10$11#7???8000$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?801030#800000000000&$2#10!$2-8,8$3<!$2-10,8$3=!$2-18,8$3>!$2-20,8$3?'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190)$2-30#30$21##190#&6+$21#<#3#7???8000#1($21#<#4"%pstring).
Definition ss0 : sym_state := SS 851208 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (12), ELit 4)].
Definition F0L : list SR.region := [((EVar 33), (12), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?=34#<?=34#5=#<?=34,20#$3<$2$3$4$5$6$7$3=$3>+$21#<#$<$=$>$?$10$11$3?$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,=!$21#<,4#'$2#7???7?801030#800000000000&$2#10!$2-8,8$3<!$2-10,8$3=!$2-18,8$3>!$2-20,8$3?'$21#6;6000#7????????>70&$21#8)##7???7000#100000001000$21##190)$2-30#30$21##190#&6+$21#<#3#7???8000#1($21#<#4,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 851252 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_9a423e.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 851208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_9a423e.IT BndT_Na_002.SegItab_Na_9a423e.IT_sound BF NX0 BR XSTEP F0 PSS plan 851208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrsZ.

Module LibSegNa_qrvE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [838104].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160#1$;$<$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$15$2?+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",20'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##'$2?##1!$32#60,1&9$2<#?='$2<##??'&9$2<#1##!$2-?8,8$21!$2-=0,8$21!$2-<8,8#7???8000!$32#68,8#2!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4#&6$32#3#7???800<#4"%pstring).
Definition ss0 : sym_state := SS 818212 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-272), ELit 8); ((EVar 2), (-312), ELit 8); ((EVar 2), (-296), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-272), 8); ((EVar 2), (-312), 8); ((EVar 2), (-296), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<9=8#5=#<<9=8,20##<7?9<+$2-160$3$4$5$6$7$8+$2-160+$2-88+$32#60+$2-:8#7???8000$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000+$32#60+$21#10$21^#8#:<7230489>80000$21$19+$32#30+$32#70$1<$1=$1>$1?,,23!$2-128,8$32!$2-138,8$2?!$2-110,8+$32#60'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##'$2?##1!$32#60,1&9$2<#?='$2<##??'&9$2<#1##!$2-?8,8$21!$2-=0,8$21!$2-<8,8#7???8000!$32#68,8#2!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4#&6$32#3#7???800<#4,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818212 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818212 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvE.

Module LibSegNa_qrvEd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [838104].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160#1$;$<$=$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000#1$15$2?+$32#20+$32#60$19+$32#30$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1'$2?##1!$32#60,1&9$2<#?='$2<##??'&9$2<#1#1#1!$2-?8,8$21!$2-=0,8$21!$2-<8,8#7???8000!$32#68,8#2!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4#&6$32#3#7???800<#4!$32#78,8$2='$2=#1000#7?????????<0!$21#18,8$31'$31#1000#7?????????<0"%pstring).
Definition ss0 : sym_state := SS 818212 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-272), ELit 8); ((EVar 2), (-312), ELit 8); ((EVar 2), (-296), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-272), 8); ((EVar 2), (-312), 8); ((EVar 2), (-296), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<9=8#5=#<<9=8,20##<7?9<+$2-160$3$4$5$6$7$8+$2-160+$2-88+$32#60+$2-:8#7???8000$>$?$10$11+&6$32#3#7???8000+&6$21#3#7???8000+$32#60$31$21^#8#:<7230489>80000$21$19+$32#30$2=$1<$1=$1>$1?,,27!$2-128,8$32!$2-138,8$2?!$2-110,8+$32#60'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1'$2?##1!$32#60,1&9$2<#?='$2<##??'&9$2<#1#1#1!$2-?8,8$21!$2-=0,8$21!$2-<8,8#7???8000!$32#68,8#2!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4#&6$32#3#7???800<#4!$32#78,8$2='$2=#1000#7?????????<0!$21#18,8$31'$31#1000#7?????????<0,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818212 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818212 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvEd.

Module LibSegNa_qrvF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [838104].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$2-108,8+$32#20"%pstring).
Definition ss0 : sym_state := SS 819100 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<9=8#5=#<<9=8,20##<7?;0+$2-160$3$4$5$6$7$8+$2-160+$2-:8+$32#20+$2-;8$=$>$?$10$11$12+$32#20$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,:'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$2-108,8+$32#20,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819100 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819100 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvF.

Module LibSegNa_qrvG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [836496].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12+$32#20+$32#60$15$16$17$21$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$2-100,8$2:"%pstring).
Definition ss0 : sym_state := SS 819120 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-172), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-172), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<390#5=#<<390,20##<7?<<+$2-160$3$4$5$6$7$8+$2-160$21+$32#20+$32#60+$2-:<$>$?$10$11$12+$32#20+$32#60$15$16$2:$21$19$1:$1;$1<$1=$1>$1?,,;!$2-:<,4#'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$2-100,8$2:,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 836496 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819120 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819120 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvG.

Module LibSegNa_qrvH.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827428].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160#$;$<$=$>$?$10$11$12+$32#20+$32#60$15$21$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#20,1&9$2;#?='$2;##??'&9$2;#1##!$2-<8,8#7???8000!$32#28,8#1!$32#68,8#2"%pstring).
Definition ss0 : sym_state := SS 819148 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-336), ELit 8); ((EVar 2), (-224), ELit 8); ((EVar 2), (-216), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-336), 8); ((EVar 2), (-224), 8); ((EVar 2), (-216), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<:024#5=#<:024,20##<8008+$2-160$3$4$5$6$7$8+$2-160$21#1$<$=$>$?$10$11$12+$32#20+$32#60#7???8000$21$17$18$19$1:#2$1<$1=$1>$1?,,12!$2-=8,8#1!$2->0,8+$32#30!$2-150,8#'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#20,1&9$2;#?='$2;##??'&9$2;#1##!$2-<8,8#7???8000!$32#28,8#1!$32#68,8#2,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 827428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819148 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819148 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvH.

End BndP_Na_095.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_002.
Module BndP_Na_096.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_096 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_44d4102ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvI3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvId3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvJ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvK3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvKd3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_d06c742ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvM3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvMd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvN3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvNd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096=LibSegNa_qrvO3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvOd3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096>LibSegNa_qrvPd3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_89918d2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC202BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC203NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC202BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC205XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC202F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC203PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC204planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC205regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0222;BndP_Na_096?LibSegNa_qrzC203kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qrvI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14#7???8000$21$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##!$21#8,8#1"%pstring).
Definition ss0 : sym_state := SS 819208 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#7?058#5=#7?058,20##<8070+$2-160$3$4$5$6$7$8+$2-160+$21#10##8$=$>$?$10$11+&6$21#3#7???8000$13$14#7???8000$21$17+$21#10#1$1:$1;$1<$1=$1>$1?,,16'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##!$21#8,8#1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvI.

Module LibSegNa_qrvId.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14#7???8000$21$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1!$21#8,8#1!$21#18,8$31'$31#1000#7?????????<0"%pstring).
Definition ss0 : sym_state := SS 819208 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#7?058#5=#7?058,20##<8070+$2-160$3$4$5$6$7$8+$2-160$31##8$=$>$?$10$11+&6$21#3#7???8000$13$14#7???8000$21$17$31#1$1:$1;$1<$1=$1>$1?,,18'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1!$21#8,8#1!$21#18,8$31'$31#1000#7?????????<0,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819208 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819208 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvId.

Module LibSegNa_qrvJ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [827044].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13+$32#60$15$16$2:$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200"%pstring).
Definition ss0 : sym_state := SS 819312 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<9>:4#5=#<9>:4,20##<807<+$2-160$3$4$5$6$7$8+$2-160$2:+$32#60$<$=$>$?$10$11$12$13+$32#60$15$16$2:$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819312 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819312 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvJ.

Module LibSegNa_qrvK.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [837064].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$21#3#7???8000$13$14#7???8000$16$2:+$21#10$19$1:#2$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",29'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40)$21##20$2:##20!$2:#,1$30'$30##??'&9$30#1##!$2:#10,8$24!$2:#18,8$25'$24#^#?#???????????????'$25#1#40000000!$2-=8,8#1!$2->0,8+$32#30!$2-<8,8#7???8000!$2-=0,8$21!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4"%pstring).
Definition ss0 : sym_state := SS 819324 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-232), ELit 8); ((EVar 2), (-320), ELit 8); ((EVar 2), (-328), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-232), 8); ((EVar 2), (-320), 8); ((EVar 2), (-328), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<5<8#5=#<<5<8,20##<823<+$2-160$3$4$5$6$7$8+$2-160$21$25$24^#8#:<7230489>80000$>$?$10$11$21+$2:#10+$2:#8#8#1+$2:#10^#8#:<7230489>80000+$21#8#7???8000+$21#8$1<$1=$1>$1?,,2<!$2-148,8+&6$21#3#7???8000!$2-140,8+&6$2:#3#7???8000!$2->8,8#'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40)$21##20$2:##20!$2:#,1$30'$30##??'&9$30#1##!$2:#10,8$24!$2:#18,8$25'$24#^#?#???????????????'$25#1#40000000!$2-=8,8#1!$2->0,8+$32#30!$2-<8,8#7???8000!$2-=0,8$21!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 837064 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819324 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvK.

Module LibSegNa_qrvKd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [837064].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$21#3#7???8000$13$14#7???8000$16$2:$31$19$1:#2$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40)$21##20$2:##20!$2:#,1$30'$30##??'&9$30#1##!$2:#10,8$24!$2:#18,8$25'$24#^#?#???????????????'$25#1#40000000!$2-=8,8#1!$2->0,8+$32#30!$2-<8,8#7???8000!$2-=0,8$21!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4'$31#1000#7?????????<0"%pstring).
Definition ss0 : sym_state := SS 819324 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-232), ELit 8); ((EVar 2), (-320), ELit 8); ((EVar 2), (-328), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-232), 8); ((EVar 2), (-320), 8); ((EVar 2), (-328), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<5<8#5=#<<5<8,20##<823<+$2-160$3$4$5$6$7$8+$2-160$21$25$24^#8#:<7230489>80000$>$?$10$11$21+$2:#10+$2:#8#8#1+$2:#10^#8#:<7230489>80000+$31-8#7???8000+$31-8$1<$1=$1>$1?,,2=!$2-148,8+&6$21#3#7???8000!$2-140,8+&6$2:#3#7???8000!$2->8,8#'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40)$21##20$2:##20!$2:#,1$30'$30##??'&9$30#1##!$2:#10,8$24!$2:#18,8$25'$24#^#?#???????????????'$25#1#40000000!$2-=8,8#1!$2->0,8+$32#30!$2-<8,8#7???8000!$2-=0,8$21!$32#30,8^#8#:<7230489>80000#&6$32#3#7???8004#4'$31#1000#7?????????<0,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 837064 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819324 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819324 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvKd.

Module LibSegNa_qrvL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_d06c74.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_d06c74.IT.
Definition ENDS : list Z := [837320].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20##<823<+$2-160$3$4$5$6$7$8+$2-160#$;$2>$=$>$?$10$11$21$13+$2:#8#8$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2>#1#7???????'$2:#6;6000#7?????????>0!$2->0,8+$32#30!$2-=8,8#1"%pstring).
Definition ss0 : sym_state := SS 837312 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<6<8#5=#<<6<8,20##<8258+$2-160$3$4$5$6$7$8+$2-160$21+$2:#10+$32#30#1+$2-;8$?$10$11$21$13+$2:#8#8$16$17$18$19$1:$1;$1<$1=$1>$1?,,>!$2-;8,8$2>'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2>#1#7???????'$2:#6;6000#7?????????>0!$2->0,8+$32#30!$2-=8,8#1,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 837320 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_d06c74.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 837312 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_d06c74.IT BndT_Na_002.SegItab_Na_d06c74.IT_sound BF NX0 BR XSTEP F0 PSS plan 837312 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvL.

Module LibSegNa_qrvM.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [830872].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12+$2:#10+$2:#8#8#1+$2:#10$18+$21#8#7???8000+$21#8$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0'$2>#1#7???????!$2-;8,8$2>!$2->8,8#!$2-?8,8$21!$2-118,8$32!$2-128,8$32!$2-108,8+$32#20!$2-110,8+$32#60!$2-?0,8+&6$32#3#7???8000"%pstring).
Definition ss0 : sym_state := SS 819800 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (16), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (16), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<:=98#5=#<:=98,20##<82;8+$2-160$3$4$5$6$7$8+$2-160$21+$21#10$<$=$>$?$10$11+&6$32#3#7???8000+$2:#8+$32#20+$32#60$21+$2:#8$32$21#7???8000$32$1<$1=$1>$1?,,1=!$21#10,8$2>'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0'$2>#1#7???????!$2-;8,8$2>!$2->8,8#!$2-?8,8$21!$2-118,8$32!$2-128,8$32!$2-108,8+$32#20!$2-110,8+$32#60!$2-?0,8+&6$32#3#7???8000,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819800 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvM.

Module LibSegNa_qrvMd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [830872].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12+$2:#10+$2:#8#8#1+$2:#10$18+$31-8#7???8000+$31-8$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",25'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0'$2>#1#7???????!$2-;8,8$2>!$2->8,8#!$2-?8,8$21!$2-118,8$32!$2-128,8$32!$2-108,8+$32#20!$2-110,8+$32#60!$2-?0,8+&6$32#3#7???8000'$31#1000#7?????????<0&$31#10)##7???7000#100000001000$31##40#&6$31#3#7???8000#8($31##40)$31##40$21##20)$31##40$2:##20)$31##40$32##200)$2-160#170$31##40"%pstring).
Definition ss0 : sym_state := SS 819800 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 49), (0), ELit 8)].
Definition F0L : list SR.region := [((EVar 49), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<:=98#5=#<:=98,20##<82;8+$2-160$3$4$5$6$7$8+$2-160$21$31$<$=$>$?$10$11+&6$32#3#7???8000+$2:#8+$32#20+$32#60$21+$2:#8$32+$31-10#7???8000$32$1<$1=$1>$1?,,26!$31#,8$2>'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0'$2>#1#7???????!$2-;8,8$2>!$2->8,8#!$2-?8,8$21!$2-118,8$32!$2-128,8$32!$2-108,8+$32#20!$2-110,8+$32#60!$2-?0,8+&6$32#3#7???8000'$31#1000#7?????????<0&$31#10)##7???7000#100000001000$31##40#&6$31#3#7???8000#8($31##40)$31##40$21##20)$31##40$2:##20)$31##40$32##200)$2-160#170$31##40,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819800 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819800 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvMd.

Module LibSegNa_qrvN.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [837920].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14$15$21$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1##'$2?##1'$2:#6;6000#7?????????>0!$2-100,8$2:!$2-140,8+&6$2:#3#7???8000!$2-148,8+&6$21#3#7???8000!$2-=0,8$21!$2-138,8$2?!$2-130,8#1!$2-:<,4#!$2-150,8#"%pstring).
Definition ss0 : sym_state := SS 819896 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<920#5=#<<920,20##<8304+$2-160$3$4$5$6$7$8+$2-160$21$2:##$>$?$10$11$12$2:$14$15$21+&6$2:#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,1?!$21#,1&8&9$26#?=@#2$2?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$26##??'&9$26#1##'$2?##1'$2:#6;6000#7?????????>0!$2-100,8$2:!$2-140,8+&6$2:#3#7???8000!$2-148,8+&6$21#3#7???8000!$2-=0,8$21!$2-138,8$2?!$2-130,8#1!$2-:<,4#!$2-150,8#,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 837920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819896 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819896 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvN.

Module LibSegNa_qrvNd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [837920].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14$15$21$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40!$21#,1$26'$26##??'&9$26#1#1#1'$2?##1'$2:#6;6000#7?????????>0!$2-100,8$2:!$2-140,8+&6$2:#3#7???8000!$2-148,8+&6$21#3#7???8000!$2-=0,8$21!$2-138,8$2?!$2-130,8#1!$2-:<,4#!$2-150,8#"%pstring).
Definition ss0 : sym_state := SS 819896 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<<920#5=#<<920,20##<8304+$2-160$3$4$5$6$7$8+$2-160$21$2:##$>$?$10$11$12$2:$14$15$21+&6$2:#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,1?!$21#,1&8&9$26#?=@#2$2?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$26##??'&9$26#1#1#1'$2?##1'$2:#6;6000#7?????????>0!$2-100,8$2:!$2-140,8+&6$2:#3#7???8000!$2-148,8+&6$21#3#7???8000!$2-=0,8$21!$2-138,8$2?!$2-130,8#1!$2-:<,4#!$2-150,8#,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 837920 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819896 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819896 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvNd.

Module LibSegNa_qrvO.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [820460].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$2:$14$15$16+&6$2:#3#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1<'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40!$2:#,1$38'$38##??'$26##??!$2-120,8&9$26#2!$2-:8,1$36'$36##??'&9$36#1##!$2-88,1$37'$37##??'&9$37#1##"%pstring).
Definition ss0 : sym_state := SS 819972 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#<84><#5=#<84><,20#$1+$2-160$3$4$5$6$7$8+$2-160#&9$26#2$<$=$>$?$10$11$12$2:$14$15$16+&6$2:#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,1<!$2:#,1&8&9$38#?=&9$26#2'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40'$38##??'$26##??!$2-120,8&9$26#2!$2-:8,1$36'$36##??'&9$36#1##!$2-88,1$37'$37##??'&9$37#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvO.

Module LibSegNa_qrvOd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 827428; 836496; 837064; 837320; 830872; 837920; 991168; 820460] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$2:$14$15$16+&6$2:#3#7???8000$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40!$2:#,1$38'$38##??'$26##??!$2-120,8&9$26#2!$2-:8,1$36'$36##??'&9$36#1##!$2-88,1$37'$37##??'&9$37#1#1#1!$2-70,8$39'$39#1000#7?????????<0!$2-78,8#8"%pstring).
Definition ss0 : sym_state := SS 819972 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,11#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<:024#<<390#<<5<8#<<6<8#<:=98#<<920#?1?<0#<84><#?1?<0#5=#?1?<0,20##<8360+$2-160$3$4$5$6$7$8+$2-160$39#40$<$=$>$?$10$11$12$2:$14$15$16+&6$2:#3#7???8000$18$19$1:$1;$1<$1=$1>$1?,,1?!$2:#,1&8&9$38#?=&9$26#2'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40'$38##??'$26##??!$2-120,8&9$26#2!$2-:8,1$36'$36##??'&9$36#1##!$2-88,1$37'$37##??'&9$37#1#1#1!$2-70,8$39'$39#1000#7?????????<0!$2-78,8#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 819972 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 819972 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvOd.

Module LibSegNa_qrvPd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [991168].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14+$32#60$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#60,1&9$2<#?='$2<##??'&9$2<#1#1#1!$32#78,8$2='$2=#1000#7?????????<0!$32#70,8#8"%pstring).
Definition ss0 : sym_state := SS 820064 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#?1?<0#5=#?1?<0,20##<850<+$2-160$3$4$5$6$7$8+$2-160$2=#40$<$=$>$?$10$11$12$13$14+$32#60$16$17$18$19$1:$1;$1<$1=$1>$1?,,?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#60,1&9$2<#?='$2<##??'&9$2<#1#1#1!$32#78,8$2='$2=#1000#7?????????<0!$32#70,8#8,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 820064 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 820064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qrvPd.

Module LibSegNa_qrzC20.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,6#<:1?0#<:2<<#<:1<0#<:32<#<:164#<:1?0#5=#<:1?0,20#$1$2$3$4$5$6$7$8$9#$;$<$=$>$?$10$11$12#$21+$21#8$16$17#7???8000#2+&6+$21#8#3#7???8000$1;$1<$1=$1>$1?,,9!$21#8,8#'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##,50!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
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
End LibSegNa_qrzC20.

End BndP_Na_096.
