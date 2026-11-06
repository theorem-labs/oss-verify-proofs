(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_001. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_018.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_000 BndT_Na_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_018 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_3293a72ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018?LibSegNa_aviE1w3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn322BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn322BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn325XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn324planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn642BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn642BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn645XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn644planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJn643kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp162BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp163NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp162BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp165XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp162F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp163PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp164planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp165regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp163kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp322BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp323NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp322BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp325XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp322F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp323PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp324planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp325regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp323kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp642BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp643NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp642BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp645XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp642F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp643PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp644planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp645regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_aviJp643kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018=LibSegNa_avlE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_018@LibSegNa_avlF1P53kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_aviE1w.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796304].
Definition STOPS1 : list Z := [796304] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-40#40$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-8#3#7???8000#1)$27-18#18$2-40#40)$27-18#18$:##38!$27-8,8^#?#???????????????!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31"%pstring).
Definition ss0 : sym_state := SS 796188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<2690#<2690#5=#<2690,20#$2<$2$3$4$5$6$7$2=$2>#1#$39$=$>$?$10$11$2?$30$31$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,21!$27-8,8#'$2#7???7?801040#800000000000&$2#10($2-40#40'$:#1000#7?????????<8&$:#8)##7???7000#100000001000$:##38#&6$:#3#7???8000#7($:##38)$2-40#40$:##38#&6+$:#8#3#7???8000#1#&6+$:#18#3#7???8000#1#&6+$:#20#3#7???8000#1!$:#8,8$29'$29#1000#7?????????>8&$29#8!$:#18,8$26!$:#20,8$27'$26#1000#800000000000'$27#1018#800000000000&$27#8'+$27@-1$26#18#186:0($27-18#18)##7???7000#100000001000+$27-18##18#&6+$27-8#3#7???8000#1)$27-18#18$2-40#40)$27-18#18$:##38!$2-8,8$2<!$2-10,8$2=!$2-18,8$2>!$2-20,8$2?!$2-28,8$30!$2-30,8$31,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796304 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 796188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 796188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviE1w.

Module LibSegNa_aviJn16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796188].
Definition STOPS1 : list Z := [796188] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1376256 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 796408 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<261<#<261<#5=#<261<,20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 796408 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 796408 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviJn16.

Module LibSegNa_aviJn32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796188].
Definition STOPS1 : list Z := [796188] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1376256 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 796472 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<261<#<261<#5=#<261<,20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 796472 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 796472 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviJn32.

Module LibSegNa_aviJn64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796188].
Definition STOPS1 : list Z := [796188] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1376256 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 796064 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<261<#<261<#5=#<261<,20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 796064 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 796064 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviJn64.

Module LibSegNa_aviJp16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796188].
Definition STOPS1 : list Z := [796188] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1376256 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 796356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<261<#<261<#5=#<261<,20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 796356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 796356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviJp16.

Module LibSegNa_aviJp32.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796188].
Definition STOPS1 : list Z := [796188] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1376256 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 796440 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<261<#<261<#5=#<261<,20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 796440 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 796440 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviJp32.

Module LibSegNa_aviJp64.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_3293a7.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_3293a7.IT.
Definition ENDS : list Z := [796188].
Definition STOPS1 : list Z := [796188] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 1376256 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487232 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-64)) (ELit 64)].
Definition ss0 : sym_state := SS 795984 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<261<#<261<#5=#<261<,20#$1+$2-40$3$4$5$6$7$:$;$37$38$39$=$>$?$10$11$25#7???8000$3:$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,6%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 796188 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_3293a7.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 795984 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_3293a7.IT BndT_Na_000.SegItab_Na_3293a7.IT_sound BF NX0 BR XSTEP F0 PSS plan 795984 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_aviJp64.

Module LibSegNa_avlB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841156; 841832].
Definition STOPS1 : list Z := [841156; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 0 140737488355328;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 0 140737488355328].
Definition ss0 : sym_state := SS 841644 regs0 [] kn0 NX0.
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

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5<4#<=868#<=5<4#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21$23#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?,,4'&4&1$21+$21$23#1#1#1'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5<4#<=868#<=5<4#<=868#5=#<=5<4,20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?,,4'&4&1$21+$21$23#1##'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 841156 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841644 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841644 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlB.

Module LibSegNa_avlE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841156; 841832].
Definition STOPS1 : list Z := [841156; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 35); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##1???????"%pstring).
Definition ss0 : sym_state := SS 841016 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5<4#<=868#<=5<4#<=868#5;#<=56<,20#$1+$2-60$3$4$5$6$7$8$9$21$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##1???????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5<4#<=868#<=5<4#<=868#5=#<=868,20#$1+$2-60$3$4$5$6$7$8$9$21$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15'&4&1$23##1#1#1!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##1???????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5<4#<=868#<=5<4#<=868#5=#<=5<4,20#$1+$2-60$3$4#?5^#?#?????????????;?#>?#?0#90$21#15?:78$21$=+$21$23#8#1^#?#?????????????<2#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?,,15'&4&1$23##1##!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##1???????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841156 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841016 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841016 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlE.

Module LibSegNa_avlF1P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P1.

Module LibSegNa_avlF1P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#2$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#2$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#2$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P2.

Module LibSegNa_avlF1P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#3$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#3$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#3$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P3.

Module LibSegNa_avlF1P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#4$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#4$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#4$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P4.

Module LibSegNa_avlF1P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#5$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#5$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#5$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P5.

End BndP_Na_018.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001.
Module BndP_Na_022.
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
Ltac2 kr_t_BndP_Na_022 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF6Z3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlF7P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022?LibSegNa_avlF7Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022>LibSegNa_avlHf3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_022@LibSegNa_avlHsP43kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlF6Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??#&6+$21#6#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??#&6+$21#6#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??#&6+$21#6#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??#&6+$21#6#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6Z.

Module LibSegNa_avlF7P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#1'&9+$21#7#7##"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#1'&9+$21#7#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#1'&9+$21#7#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#1+$21#8#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#1'&9+$21#7#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P1.

Module LibSegNa_avlF7P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#2'&9+$21#7#7##1"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#2$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#2'&9+$21#7#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#2$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#2'&9+$21#7#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#2+$21#8&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#2'&9+$21#7#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P2.

Module LibSegNa_avlF7P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#3'&9+$21#7#7##2"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#3$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#3'&9+$21#7#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#3$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#3'&9+$21#7#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#3+$21#8&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#3'&9+$21#7#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P3.

Module LibSegNa_avlF7P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#4'&9+$21#7#7##3"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#4$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#4'&9+$21#7#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#4$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#4'&9+$21#7#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#4+$21#8&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#4'&9+$21#7#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P4.

Module LibSegNa_avlF7P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#5'&9+$21#7#7##4"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#5$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#5'&9+$21#7#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#5$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#5'&9+$21#7#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#5+$21#8&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#5'&9+$21#7#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P5.

Module LibSegNa_avlF7P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#6'&9+$21#7#7##5"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#6$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#6'&9+$21#7#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#6$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#6'&9+$21#7#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#6+$21#8&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#6'&9+$21#7#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P6.

Module LibSegNa_avlF7P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#7'&9+$21#7#7##6"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#7$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#7'&9+$21#7#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#7$21&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#7'&9+$21#7#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#7+$21#8&9+$21#7#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??!&6+$21#7#3#7???8000,1#7'&9+$21#7#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7P7.

Module LibSegNa_avlF7Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396; 841644].
Definition STOPS1 : list Z := [841396; 841644] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??#&6+$21#7#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841356 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5;#<=6:4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??#&6+$21#7#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??#&6+$21#7#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=6;4#<=7:<#<=6;4#<=7:<#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#7#+$21#8$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#7,1$24'$24##??#&6+$21#7#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841356 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841356 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF7Z.

Module LibSegNa_avlHf.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841188; 841396].
Definition STOPS1 : list Z := [841188; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 8 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 1)].
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5>4#<=6;4#<=5>4#<=6;4#5;#<=5>0,20#$1+$2-60$3$4#?5-41#>?#?0#90$23$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#,1$24'$24##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5>4#<=6;4#<=5>4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#,1$24'$24##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=5>4#<=6;4#<=5>4#<=6;4#5=#<=5>4,20#$1+$2-60$3$4#?5-41#>?#?0#90$23$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#,1$24'$24##??#&6$21#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841188 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHf.

Module LibSegNa_avlHsP1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#1'&9$21#7##"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#1'&9$21#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP1.

Module LibSegNa_avlHsP2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#2'&9$21#7##1"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$21#7$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#2'&9$21#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP2.

Module LibSegNa_avlHsP3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#3'&9$21#7##2"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$21#7$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#3'&9$21#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP3.

Module LibSegNa_avlHsP4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#4'&9$21#7##3"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$21#7$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#4'&9$21#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP4.

End BndP_Na_022.
Module BndP_Na_023.
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
Ltac2 kr_t_BndP_Na_023 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP52BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP55XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP53kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlHsP73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlHsZ3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023=LibSegNa_avlL3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR1P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023?LibSegNa_avlR1Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_023@LibSegNa_avlR2P13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlHsP5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#5'&9$21#7##4"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$21#7$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#5'&9$21#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP5.

Module LibSegNa_avlHsP6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#6'&9$21#7##5"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$21#7$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#6'&9$21#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP6.

Module LibSegNa_avlHsP7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#7'&9$21#7##6"%pstring).
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$21#7$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??!&6$21#3#7???8000,1#7'&9$21#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsP7.

Module LibSegNa_avlHsZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841396].
Definition STOPS1 : list Z := [841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 7;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KWord (SA (EVar 33) 0) 1 (EVar 36);
   KRange (EVar 36) 0 255;
   KZero (SA (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) 2147450880) (ELit 1)].
Definition ss0 : sym_state := SS 841156 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6;4#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#1#7'+$21$23#1#800000000000!$21#,1$24'$24##??#&6$21#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841156 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841156 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlHsZ.

Module LibSegNa_avlL.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841644; 841832].
Definition STOPS1 : list Z := [841644; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$27$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255;
   KRange (EVar 34) 0 140737488355328].
Definition ss0 : sym_state := SS 841568 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=764,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,5'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=778,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,6'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=7:8,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,7'&4&1$25#?0#1#1#1'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&9$27#??#90#1#1'&4&1$25#?0#1#1#1'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&9$27#??#90##'&4&1$25#?0#1#1#1'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition ex9 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=77<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,7'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).

Definition arms10 := Eval vm_compute in (match SGP.branch_probe IT s9 with Some e => SGP.case_arms s9 e 0 | None => None end).
Definition f10 : sym_state := match arms10 with Some (Some s, _) => s | _ => s9 end.
Definition t10 : sym_state := match arms10 with Some (_, Some s) => s | _ => s9 end.

Definition ex11 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=780,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).

Definition arms12 := Eval vm_compute in (match SGP.branch_probe IT s11 with Some e => SGP.case_arms s11 e 0 | None => None end).
Definition f12 : sym_state := match arms12 with Some (Some s, _) => s | _ => s11 end.
Definition t12 : sym_state := match arms12 with Some (_, Some s) => s | _ => s11 end.

Definition ex13 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,9'&4#8?&9$27#??#1#1'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s13 : sym_state := snd (snd ex13).

Definition ex14 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,9'&4#8?&9$27#??##'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).

Definition ex15 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=794,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s15 : sym_state := snd (snd ex15).

Definition arms16 := Eval vm_compute in (match SGP.branch_probe IT s15 with Some e => SGP.case_arms s15 e 0 | None => None end).
Definition f16 : sym_state := match arms16 with Some (Some s, _) => s | _ => s15 end.
Definition t16 : sym_state := match arms16 with Some (_, Some s) => s | _ => s15 end.

Definition ex17 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,9'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s17 : sym_state := snd (snd ex17).

Definition ex18 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=798,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,9'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).

Definition arms19 := Eval vm_compute in (match SGP.branch_probe IT s18 with Some e => SGP.case_arms s18 e 0 | None => None end).
Definition f19 : sym_state := match arms19 with Some (Some s, _) => s | _ => s18 end.
Definition t19 : sym_state := match arms19 with Some (_, Some s) => s | _ => s18 end.

Definition ex20 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,:'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).

Definition ex21 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,:'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).

Definition ex22 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=768,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,6'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).

Definition arms23 := Eval vm_compute in (match SGP.branch_probe IT s22 with Some e => SGP.case_arms s22 e 0 | None => None end).
Definition f23 : sym_state := match arms23 with Some (Some s, _) => s | _ => s22 end.
Definition t23 : sym_state := match arms23 with Some (_, Some s) => s | _ => s22 end.

Definition ex24 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=7:0,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,7'&4&1$25#>0#1#1#1'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).

Definition arms25 := Eval vm_compute in (match SGP.branch_probe IT s24 with Some e => SGP.case_arms s24 e 0 | None => None end).
Definition f25 : sym_state := match arms25 with Some (Some s, _) => s | _ => s24 end.
Definition t25 : sym_state := match arms25 with Some (_, Some s) => s | _ => s24 end.

Definition ex26 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&9$27#??#:0#1#1'&4&1$25#>0#1#1#1'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s26 : sym_state := snd (snd ex26).

Definition ex27 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&9$27#??#:0##'&4&1$25#>0#1#1#1'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s27 : sym_state := snd (snd ex27).

Definition ex28 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=76<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,7'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s28 : sym_state := snd (snd ex28).

Definition arms29 := Eval vm_compute in (match SGP.branch_probe IT s28 with Some e => SGP.case_arms s28 e 0 | None => None end).
Definition f29 : sym_state := match arms29 with Some (Some s, _) => s | _ => s28 end.
Definition t29 : sym_state := match arms29 with Some (_, Some s) => s | _ => s28 end.

Definition ex30 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=770,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s30 : sym_state := snd (snd ex30).

Definition arms31 := Eval vm_compute in (match SGP.branch_probe IT s30 with Some e => SGP.case_arms s30 e 0 | None => None end).
Definition f31 : sym_state := match arms31 with Some (Some s, _) => s | _ => s30 end.
Definition t31 : sym_state := match arms31 with Some (_, Some s) => s | _ => s30 end.

Definition ex32 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,9'&4#9?&9$27#??#1#1'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s32 : sym_state := snd (snd ex32).

Definition ex33 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21&9$27#??$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,9'&4#9?&9$27#??##'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s33 : sym_state := snd (snd ex33).

Definition ex34 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=794,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,8'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s34 : sym_state := snd (snd ex34).

Definition arms35 := Eval vm_compute in (match SGP.branch_probe IT s34 with Some e => SGP.case_arms s34 e 0 | None => None end).
Definition f35 : sym_state := match arms35 with Some (Some s, _) => s | _ => s34 end.
Definition t35 : sym_state := match arms35 with Some (_, Some s) => s | _ => s34 end.

Definition ex36 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,9'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s36 : sym_state := snd (snd ex36).

Definition ex37 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=798,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,9'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s37 : sym_state := snd (snd ex37).

Definition arms38 := Eval vm_compute in (match SGP.branch_probe IT s37 with Some e => SGP.case_arms s37 e 0 | None => None end).
Definition f38 : sym_state := match arms38 with Some (Some s, _) => s | _ => s37 end.
Definition t38 : sym_state := match arms38 with Some (_, Some s) => s | _ => s37 end.

Definition ex39 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,:'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s39 : sym_state := snd (snd ex39).

Definition ex40 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6$22&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25$19$1:$1;#>0#:0#>=#9?,,:'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s40 : sym_state := snd (snd ex40).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PEnd 0)) (SGA.mkplan (fst ex8) (SGP.PEnd 1)))) (SGA.mkplan (fst ex9) (SGP.PBranch (SGA.mkplan (fst ex11) (SGP.PBranch (SGA.mkplan (fst ex13) (SGP.PEnd 2)) (SGA.mkplan (fst ex14) (SGP.PEnd 3)))) (SGA.mkplan (fst ex15) (SGP.PBranch (SGA.mkplan (fst ex17) (SGP.PEnd 4)) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PEnd 5)) (SGA.mkplan (fst ex21) (SGP.PEnd 6)))))))))) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PBranch (SGA.mkplan (fst ex26) (SGP.PEnd 7)) (SGA.mkplan (fst ex27) (SGP.PEnd 8)))) (SGA.mkplan (fst ex28) (SGP.PBranch (SGA.mkplan (fst ex30) (SGP.PBranch (SGA.mkplan (fst ex32) (SGP.PEnd 9)) (SGA.mkplan (fst ex33) (SGP.PEnd 10)))) (SGA.mkplan (fst ex34) (SGP.PBranch (SGA.mkplan (fst ex36) (SGP.PEnd 11)) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PEnd 12)) (SGA.mkplan (fst ex40) (SGP.PEnd 13))))))))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s8).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s8).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s13).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s13).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s13 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s13 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s13).
Definition ps2 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition regs_out3 : list expr := Eval vm_compute in (s_regs s14).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s14).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s14 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s14 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s14).
Definition ps3 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out3 (ELit 0))) (seq 1 31)) F0L cells3.

Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out4 (ELit 0))) (seq 1 31)) F0L cells4.

Definition regs_out5 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s20).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s20).
Definition ps5 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out5 (ELit 0))) (seq 1 31)) F0L cells5.

Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out6 (ELit 0))) (seq 1 31)) F0L cells6.

Definition regs_out7 : list expr := Eval vm_compute in (s_regs s26).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s26).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s26 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s26 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s26).
Definition ps7 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out7 (ELit 0))) (seq 1 31)) F0L cells7.

Definition regs_out8 : list expr := Eval vm_compute in (s_regs s27).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s27).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s27 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s27 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s27).
Definition ps8 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out8 (ELit 0))) (seq 1 31)) F0L cells8.

Definition regs_out9 : list expr := Eval vm_compute in (s_regs s32).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s32).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s32 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s32 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s32).
Definition ps9 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out9 (ELit 0))) (seq 1 31)) F0L cells9.

Definition regs_out10 : list expr := Eval vm_compute in (s_regs s33).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s33).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s33 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s33 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s33).
Definition ps10 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out10 (ELit 0))) (seq 1 31)) F0L cells10.

Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out11 (ELit 0))) (seq 1 31)) F0L cells11.

Definition regs_out12 : list expr := Eval vm_compute in (s_regs s39).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s39).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s39 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s39 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s39).
Definition ps12 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out12 (ELit 0))) (seq 1 31)) F0L cells12.

Definition regs_out13 : list expr := Eval vm_compute in (s_regs s40).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s40).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s40 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s40 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s40).
Definition ps13 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out13 (ELit 0))) (seq 1 31)) F0L cells13.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841568 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841568 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlL.

Module LibSegNa_avlR1P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P1.

Module LibSegNa_avlR1P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#2'&9+$21#1#7##1'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P2.

Module LibSegNa_avlR1P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#3'&9+$21#1#7##2'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P3.

Module LibSegNa_avlR1P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#4'&9+$21#1#7##3'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P4.

Module LibSegNa_avlR1P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#5'&9+$21#1#7##4'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P5.

Module LibSegNa_avlR1P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P6.

Module LibSegNa_avlR1P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#1#7$1:$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1P7.

Module LibSegNa_avlR1Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841568; 841832].
Definition STOPS1 : list Z := [841568; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??#&6+$21#1#3#7???8000#1'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841540 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5;#<=75<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??#&6+$21#1#3#7???8000#1'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??#&6+$21#1#3#7???8000#1'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=760#<=868#<=760#<=868#5=#<=760,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#1+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19$1:$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??!$21#1,1$27'$27##??#&6+$21#1#3#7???8000#1'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841568 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841540 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841540 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR1Z.

Module LibSegNa_avlR2P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P1.

End BndP_Na_023.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_000.
Module BndP_Na_025.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_025 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlR3Z3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlS3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT02BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT03NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT02BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT05XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT02F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT03PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT04planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT05regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025>LibSegNa_avlT03kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT1b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT2b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025?LibSegNa_avlT3b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avlTbig3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avlX3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_037c062ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025=LibSegNa_avrE3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_025@LibSegNa_avrF1P13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlR3Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??#&6+$21#3#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??#&6+$21#3#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?,,8'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??#&6+$21#3#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?,,8'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??#&6+$21#3#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3Z.

Module LibSegNa_avlS.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841428].
Definition STOPS1 : list Z := [841428] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KZero (SA (ELit 0) 2147470790) (ELit 33)].
Definition ss0 : sym_state := SS 841396 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=6=4#<=6=4#5=#<=6=4,20#$1+$2-60$3$4#?5-41#>?#?0#90$21+&9$24#??#26>36#$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24&9$24#??$19$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000###7???<=<6#21,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841428 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841396 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841396 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlS.

Module LibSegNa_avlT0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841644; 841832].
Definition STOPS1 : list Z := [841644; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=794,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6+$21#1&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25#$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",#5;#<=794,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6+$21#1&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25#$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition arms3 := Eval vm_compute in (match SGP.branch_probe IT s2 with Some e => SGP.case_arms s2 e 0 | None => None end).
Definition f3 : sym_state := match arms3 with Some (Some s, _) => s | _ => s2 end.
Definition t3 : sym_state := match arms3 with Some (_, Some s) => s | _ => s2 end.

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6+$21#1&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25#$1:$1;#>0#:0#>=#9?,,5'&3&7@#100000000000000$24#38-3>#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).

Definition ex5 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5;#<=798,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6+$21#1&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25#$1:$1;#>0#:0#>=#9?,,5'&3&7@#100000000000000$24#38-3>##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).

Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.

Definition ex7 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=7:<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6+$21#1&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25#$1:$1;#>0#:0#>=#9?,,6'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).

Definition ex8 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=7:<#<=868#<=7:<#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#6+$21#1&7@#100000000000000$24#38+$21$23#8#1-3>#7???8000#?4#8?#2#3@#100000000000000$24$25#$1:$1;#>0#:0#>=#9?,,6'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGA.mkplan (fst ex2) (SGP.PBranch (SGA.mkplan (fst ex4) (SGP.PEnd 0)) (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PEnd 1)) (SGA.mkplan (fst ex8) (SGP.PEnd 2)))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s7).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s7).
Definition ps1 : SR.post_spec := SR.PS 841644 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition regs_out2 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s8).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s8).
Definition ps2 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out2 (ELit 0))) (seq 1 31)) F0L cells2.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1; ps2] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT0.

Module LibSegNa_avlT1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841832].
Definition STOPS1 : list Z := [841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#1$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 1;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=868#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#5$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#1$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#1#1'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT1a.

Module LibSegNa_avlT1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540].
Definition STOPS1 : list Z := [841540] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#1$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 2 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=744#<=744#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#1+$21#2+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#1$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#2#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT1b.

Module LibSegNa_avlT2a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841832].
Definition STOPS1 : list Z := [841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#2$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 2;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=868#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#5$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#2$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#1#2'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT2a.

Module LibSegNa_avlT2b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512].
Definition STOPS1 : list Z := [841512] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#2$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 3 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=728#<=728#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#1+$21#3+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#2+$21#3$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT2b.

Module LibSegNa_avlT3a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841832].
Definition STOPS1 : list Z := [841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#3$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 3;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=868#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#5$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#3$1:$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#1#3'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT3a.

Module LibSegNa_avlT3b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841484].
Definition STOPS1 : list Z := [841484] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#3$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 4 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=70<#<=70<#5=#<=70<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#1+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#3+$21#4$1;#>0#:0#>=#9?,,4'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841484 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlT3b.

Module LibSegNa_avlTbig.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841832].
Definition STOPS1 : list Z := [841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$26$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 1 536870912;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 1 140737488355328;
   KRange (EVar 37) 0 255;
   KRange (EVar 38) 4 255].
Definition ss0 : sym_state := SS 841432 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=868#<=868#5;#<=6=<,20#$1+$2-60$3$4#?5-41#>?#?0#90$21$23$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$26$1:$1;#>0#:0#>=#9?,,5'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$26#4#??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=868#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#1++$21$26#1+$21$26+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$26++$21$26#1$1;#>0#:0#>=#9?,,6'&4$26$23#1#1'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$26#4#??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=868#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#5$<$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$26$1:$1;#>0#:0#>=#9?,,6'&4$26$23##'$21##800000000000'$23#1#20000000'+$21$23#1#800000000000'$25##??'$26#4#??,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841432 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841432 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlTbig.

Module LibSegNa_avlX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841884].
Definition STOPS1 : list Z := [841884] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",>'$2#7???7?801060#800000000000&$2#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31!$2-58,8$32!$2-60,8$33"%pstring).
Definition ss0 : sym_state := SS 841832 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<=89<#<=89<#5=#<=89<,20#$28$2$3$4$5$6$7$29$2:$:$;$<$=$>$?$10$11$2;$2<$2=$2>$2?$30$31$32$33$1;$1<$1=$1>$1?,,>'$2#7???7?801060#800000000000&$2#10!$2-8,8$28!$2-10,8$29!$2-18,8$2:!$2-20,8$2;!$2-28,8$2<!$2-30,8$2=!$2-38,8$2>!$2-40,8$2?!$2-48,8$30!$2-50,8$31!$2-58,8$32!$2-60,8$33,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 841884 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841832 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841832 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlX.

Module LibSegNa_avrB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_037c06.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_037c06.IT.
Definition ENDS : list Z := [865772; 866448].
Definition STOPS1 : list Z := [865772; 866448] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 33) 0 140737488355328;
   KRange (EVar 35) 0 140737488355328;
   KRange (EAlu Instr.ALU_ADD (EVar 33) (EVar 35)) 0 140737488355328].
Definition ss0 : sym_state := SS 866260 regs0 [] kn0 NX0.
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

Definition arms1 := Eval vm_compute in (match SGP.branch_probe IT ss0 with Some e => SGP.case_arms ss0 e 0 | None => None end).
Definition f1 : sym_state := match arms1 with Some (Some s, _) => s | _ => ss0 end.
Definition t1 : sym_state := match arms1 with Some (_, Some s) => s | _ => ss0 end.

Definition ex2 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=35><#=3890#=35><#=3890#5=#=3890,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21$23#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?,,4'&4&1$21+$21$23#1#1#1'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
Definition s2 : sym_state := snd (snd ex2).

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=35><#=3890#=35><#=3890#5=#=35><,20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?,,4'&4&1$21+$21$23#1##'$21##800000000000'$23##800000000000'+$21$23##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition plan : SGP.splan := SGP.PBranch (SGA.mkplan (fst ex2) (SGP.PEnd 0)) (SGA.mkplan (fst ex3) (SGP.PEnd 1)).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.

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
Definition ps0 : SR.post_spec := SR.PS 866448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s3).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s3).
Definition ps1 : SR.post_spec := SR.PS 865772 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_037c06.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 866260 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_037c06.IT BndT_Na_000.SegItab_Na_037c06.IT_sound BF NX0 BR XSTEP F0 PSS plan 866260 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avrB.

Module LibSegNa_avrE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_037c06.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_037c06.IT.
Definition ENDS : list Z := [865772; 866448].
Definition STOPS1 : list Z := [865772; 866448] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 35); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##3??????"%pstring).
Definition ss0 : sym_state := SS 865632 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=35><#=3890#=35><#=3890#5;#=3594,20#$1+$2-60$3$4$5$6$7$8$9$21$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,14!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=35><#=3890#=35><#=3890#5=#=3890,20#$1+$2-60$3$4$5$6$7$8$9$21$23$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,15'&4&1$23##1#1#1!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##3??????,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=35><#=3890#=35><#=3890#5=#=35><,20#$1+$2-60$3$4#?5^#?#?????????????;?#>?#?0#90$21#15?:78$21$=+$21$23#8#1^#?#?????????????<2#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?,,15'&4&1$23##1##!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801060#800000000000&$2#10($2-60#60'$21##800000000000'$23##3??????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866448 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 865772 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_037c06.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 865632 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_037c06.IT BndT_Na_000.SegItab_Na_037c06.IT_sound BF NX0 BR XSTEP F0 PSS plan 865632 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avrE.

Module LibSegNa_avrF1P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_037c06.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_037c06.IT.
Definition ENDS : list Z := [865832; 866012].
Definition STOPS1 : list Z := [865832; 866012] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##"%pstring).
Definition ss0 : sym_state := SS 865804 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=3628#=36=<#=3628#=36=<#5;#=3624,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=3628#=36=<#=3628#=36=<#5=#=36=<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#=3628#=36=<#=3628#=36=<#5=#=3628,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#1'&9+$21#1#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 866012 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 865832 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_037c06.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 865804 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_037c06.IT BndT_Na_000.SegItab_Na_037c06.IT_sound BF NX0 BR XSTEP F0 PSS plan 865804 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avrF1P1.

End BndP_Na_025.
Module BndP_Na_019.
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
Ltac2 kr_t_BndP_Na_019 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P62BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P65XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P63kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF1P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF1Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF2P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019?LibSegNa_avlF2Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_019@LibSegNa_avlF3P33kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlF1P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#6$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#6$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#6$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#6'&9+$21#1#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P6.

Module LibSegNa_avlF1P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#7$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#7$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#7$21&9+$21#1#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??!&6+$21#1#3#7???8000,1#7'&9+$21#1#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1P7.

Module LibSegNa_avlF1Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841216; 841396].
Definition STOPS1 : list Z := [841216; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??#&6+$21#1#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841188 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5;#<=5?<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??#&6+$21#1#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??#&6+$21#1#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=600#<=6;4#<=600#<=6;4#5=#<=600,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#1#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#1,1$24'$24##??#&6+$21#1#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841216 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841188 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841188 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF1Z.

Module LibSegNa_avlF2P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#1'&9+$21#2#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P1.

Module LibSegNa_avlF2P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#2$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#2$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#2$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P2.

Module LibSegNa_avlF2P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#3$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#3$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#3$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P3.

Module LibSegNa_avlF2P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#4$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#4$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#4$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P4.

Module LibSegNa_avlF2P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#5$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#5$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#5$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P5.

Module LibSegNa_avlF2P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#6$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#6$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#6$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P6.

Module LibSegNa_avlF2P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#7$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#7$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#7$21&9+$21#2#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2P7.

Module LibSegNa_avlF2Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841244; 841396].
Definition STOPS1 : list Z := [841244; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??#&6+$21#2#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841216 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5;#<=618,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??#&6+$21#2#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??#&6+$21#2#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=61<#<=6;4#<=61<#<=6;4#5=#<=61<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#2#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#2,1$24'$24##??#&6+$21#2#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841244 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841216 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841216 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF2Z.

Module LibSegNa_avlF3P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P1.

Module LibSegNa_avlF3P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#2$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#2$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#2$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P2.

Module LibSegNa_avlF3P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#3$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#3$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#3$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P3.

End BndP_Na_019.
Module BndP_Na_020.
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
Ltac2 kr_t_BndP_Na_020 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P42BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P45XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P43kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF3P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF3Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF4P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020?LibSegNa_avlF4Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_020@LibSegNa_avlF5P13kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlF3P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#4$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#4$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#4$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P4.

Module LibSegNa_avlF3P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#5$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#5$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#5$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P5.

Module LibSegNa_avlF3P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#6$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#6$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#6$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P6.

Module LibSegNa_avlF3P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#7$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#7$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#7$21&9+$21#3#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3P7.

Module LibSegNa_avlF3Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841272; 841396].
Definition STOPS1 : list Z := [841272; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??#&6+$21#3#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841244 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5;#<=634,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??#&6+$21#3#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??#&6+$21#3#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=638#<=6;4#<=638#<=6;4#5=#<=638,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#3#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#3,1$24'$24##??#&6+$21#3#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841272 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841244 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841244 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF3Z.

Module LibSegNa_avlF4P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#1'&9+$21#4#7##"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#1'&9+$21#4#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#1'&9+$21#4#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#1'&9+$21#4#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P1.

Module LibSegNa_avlF4P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#2'&9+$21#4#7##1"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#2$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#2'&9+$21#4#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#2$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#2'&9+$21#4#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#2$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#2'&9+$21#4#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P2.

Module LibSegNa_avlF4P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#3'&9+$21#4#7##2"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#3$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#3'&9+$21#4#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#3$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#3'&9+$21#4#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#3$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#3'&9+$21#4#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P3.

Module LibSegNa_avlF4P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#4'&9+$21#4#7##3"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#4$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#4'&9+$21#4#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#4$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#4'&9+$21#4#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#4$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#4'&9+$21#4#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P4.

Module LibSegNa_avlF4P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#5'&9+$21#4#7##4"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#5$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#5'&9+$21#4#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#5$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#5'&9+$21#4#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#5$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#5'&9+$21#4#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P5.

Module LibSegNa_avlF4P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#6'&9+$21#4#7##5"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#6$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#6'&9+$21#4#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#6$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#6'&9+$21#4#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#6$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#6'&9+$21#4#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P6.

Module LibSegNa_avlF4P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#7'&9+$21#4#7##6"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#7$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#7'&9+$21#4#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#7$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#7'&9+$21#4#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#7$21&9+$21#4#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??!&6+$21#4#3#7???8000,1#7'&9+$21#4#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4P7.

Module LibSegNa_avlF4Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841300; 841396].
Definition STOPS1 : list Z := [841300; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??#&6+$21#4#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841272 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5;#<=650,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??#&6+$21#4#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??#&6+$21#4#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=654#<=6;4#<=654#<=6;4#5=#<=654,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#4#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#4,1$24'$24##??#&6+$21#4#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841300 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841272 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841272 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF4Z.

Module LibSegNa_avlF5P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#1'&9+$21#5#7##"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#1'&9+$21#5#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#1'&9+$21#5#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#1'&9+$21#5#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P1.

End BndP_Na_020.
Module BndP_Na_021.
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
Ltac2 kr_t_BndP_Na_021 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P22BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P25XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P23kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF5P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021?LibSegNa_avlF5Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_021@LibSegNa_avlF6P73kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlF5P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#2'&9+$21#5#7##1"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#2$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#2'&9+$21#5#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#2$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#2'&9+$21#5#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#2$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#2'&9+$21#5#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P2.

Module LibSegNa_avlF5P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#3'&9+$21#5#7##2"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#3$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#3'&9+$21#5#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#3$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#3'&9+$21#5#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#3$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#3'&9+$21#5#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P3.

Module LibSegNa_avlF5P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#4'&9+$21#5#7##3"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#4$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#4'&9+$21#5#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#4$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#4'&9+$21#5#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#4$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#4'&9+$21#5#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P4.

Module LibSegNa_avlF5P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#5'&9+$21#5#7##4"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#5$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#5'&9+$21#5#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#5$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#5'&9+$21#5#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#5$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#5'&9+$21#5#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P5.

Module LibSegNa_avlF5P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#6'&9+$21#5#7##5"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#6$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#6'&9+$21#5#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#6$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#6'&9+$21#5#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#6$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#6'&9+$21#5#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P6.

Module LibSegNa_avlF5P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#7'&9+$21#5#7##6"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#7$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#7'&9+$21#5#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#7$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#7'&9+$21#5#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#7$21&9+$21#5#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??!&6+$21#5#3#7???8000,1#7'&9+$21#5#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5P7.

Module LibSegNa_avlF5Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841328; 841396].
Definition STOPS1 : list Z := [841328; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??#&6+$21#5#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 841300 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5;#<=66<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,6'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??#&6+$21#5#3#7???8000#1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??#&6+$21#5#3#7???8000#1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=670#<=6;4#<=670#<=6;4#5=#<=670,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#5#$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#5,1$24'$24##??#&6+$21#5#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841328 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841300 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841300 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF5Z.

Module LibSegNa_avlF6P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#1'&9+$21#6#7##"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#1'&9+$21#6#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#1'&9+$21#6#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#1$21#+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#1'&9+$21#6#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P1.

Module LibSegNa_avlF6P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#2'&9+$21#6#7##1"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#2$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#2'&9+$21#6#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#2$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#2'&9+$21#6#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#2$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#2'&9+$21#6#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P2.

Module LibSegNa_avlF6P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#3'&9+$21#6#7##2"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#3$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#3'&9+$21#6#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#3$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#3'&9+$21#6#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#3$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#3'&9+$21#6#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P3.

Module LibSegNa_avlF6P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#4'&9+$21#6#7##3"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#4$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#4'&9+$21#6#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#4$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#4'&9+$21#6#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#4$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#4'&9+$21#6#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P4.

Module LibSegNa_avlF6P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#5'&9+$21#6#7##4"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#5$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#5'&9+$21#6#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#5$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#5'&9+$21#6#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#5$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#5'&9+$21#6#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P5.

Module LibSegNa_avlF6P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#6'&9+$21#6#7##5"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#6$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#6'&9+$21#6#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#6$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#6'&9+$21#6#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#6$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#6'&9+$21#6#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P6.

Module LibSegNa_avlF6P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841356; 841396].
Definition STOPS1 : list Z := [841356; 841396] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$:$;$21$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#7'&9+$21#6#7##6"%pstring).
Definition ss0 : sym_state := SS 841328 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5;#<=688,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#7$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,7'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#7'&9+$21#6#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=6;4,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#7$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24##1#1'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#7'&9+$21#6#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=68<#<=6;4#<=68<#<=6;4#5=#<=68<,20#$1+$2-60$3$4#?5-41#>?#?0#90+$21#6#7$21&9+$21#6#7+$21$23#8#1-3>#7???8000#?4#8?#2#3],,1$24$18$19$1:$1;#>0#:0#>=#9?,,8'&3],,1$24###'$21##800000000000'$23#8#20000000'+$21$23#1#800000000000!$21#6,1$24'$24##??!&6+$21#6#3#7???8000,1#7'&9+$21#6#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841396 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841356 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841328 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841328 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlF6P7.

End BndP_Na_021.
Module BndP_Na_024.
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
Ltac2 kr_t_BndP_Na_024 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_6a38532ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P22BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P25XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P23kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR2P73kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z5XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024?LibSegNa_avlR2Z3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P15XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P25XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P35XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P45XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P52BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P53NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P52BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P55XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P52F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P53PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P54planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P55regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P53kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P62BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P63NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P62BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P65XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P62F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P63PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P64planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P65regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P63kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P72BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P73NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P72BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P75XSTEPC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P72F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P73PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P74planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P75regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0216;BndP_Na_024@LibSegNa_avlR3P73kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_avlR2P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#2'&9+$21#2#7##1'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P2.

Module LibSegNa_avlR2P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#3'&9+$21#2#7##2'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P3.

Module LibSegNa_avlR2P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#4'&9+$21#2#7##3'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P4.

Module LibSegNa_avlR2P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#5'&9+$21#2#7##4'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P5.

Module LibSegNa_avlR2P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#6'&9+$21#2#7##5'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P6.

Module LibSegNa_avlR2P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,9'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#2#7+$21#3$1;#>0#:0#>=#9?,,:'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??!&6+$21#2#3#7???8000,1#7'&9+$21#2#7##6'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2P7.

Module LibSegNa_avlR2Z.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841540; 841832].
Definition STOPS1 : list Z := [841540; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;$22$=+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??#&6+$21#2#3#7???8000#1'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 841512 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5;#<=740,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??#&6+$21#2#3#7???8000#1'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??#&6+$21#2#3#7???8000#1'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=744#<=868#<=744#<=868#5=#<=744,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27$22+$21#2+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#3#20000000'+$21$23#1#800000000000'$25##??!$21#2,1$27'$27##??#&6+$21#2#3#7???8000#1'$22##800000000000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841540 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841512 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841512 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR2Z.

Module LibSegNa_avlR3P1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25#+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#1'&9+$21#3#7##,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P1.

Module LibSegNa_avlR3P2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#2'&9+$21#3#7##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P2.

Module LibSegNa_avlR3P3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#3'&9+$21#3#7##2,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P3.

Module LibSegNa_avlR3P4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#4'&9+$21#3#7##3,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P4.

Module LibSegNa_avlR3P5.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#5'&9+$21#3#7##4,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P5.

Module LibSegNa_avlR3P6.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#6'&9+$21#3#7##5,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P6.

Module LibSegNa_avlR3P7.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_6a3853.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_6a3853.IT.
Definition ENDS : list Z := [841512; 841832].
Definition STOPS1 : list Z := [841512; 841832] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-60$3$4#?5-41#>?#?0#90$21$;+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25$19+$21#4$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6"%pstring).
Definition ss0 : sym_state := SS 841484 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5;#<=724,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,8'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).

Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.

Definition ex3 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=868,20#$1+$2-60$3$4#?5-41#>?#?0#90$21#2+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27#1#1'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).

Definition ex4 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<=728#<=868#<=728#<=868#5=#<=728,20#$1+$2-60$3$4#?5-41#>?#?0#90$21],,1$27+$21#4+$21#3+$21$23#8#1-3>#7???8000#?4#8?#2#3$24$25&9+$21#3#7+$21#3$1;#>0#:0#>=#9?,,9'&3-41],,1$27##'$21##800000000000'$23#4#20000000'+$21$23#1#800000000000'$25##??!$21#3,1$27'$27##??!&6+$21#3#3#7???8000,1#7'&9+$21#3#7##6,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 841832 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition regs_out1 : list expr := Eval vm_compute in (s_regs s4).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s4).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s4 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s4 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s4).
Definition ps1 : SR.post_spec := SR.PS 841512 (map (fun i => (i, nth i regs_out1 (ELit 0))) (seq 1 31)) F0L cells1.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0; ps1] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_6a3853.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 841484 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_6a3853.IT BndT_Na_001.SegItab_Na_6a3853.IT_sound BF NX0 BR XSTEP F0 PSS plan 841484 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_avlR3P7.

End BndP_Na_024.
