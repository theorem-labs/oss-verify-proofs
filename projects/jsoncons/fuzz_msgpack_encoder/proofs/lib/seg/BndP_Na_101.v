(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_003 BndT_Na_002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_101 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_of_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_44d4102ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ5XSTEPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthJ3kn0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthPd3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthX3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qthXd3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qthZ3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_003ASegItab_Na_e24eef2ITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmA3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB02BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB03NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB02BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB05XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB02F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB03PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB04planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB05regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB12BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB13NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB12BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB15XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB12F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB13PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB14planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB15regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtmB13kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtmC3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_8edc8b2ITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtvI3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_002ASegItab_Na_b3c5092ITC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA02BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA03NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA02BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA05XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA02F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA03PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA04planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA05regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwA03kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA162BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA163NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA162BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA165XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA162F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA163PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA164planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA165regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101?LibSegNa_qtwA163kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB2BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB3NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB2BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB5XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB2F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB3PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB4planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB5regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101=LibSegNa_qtwB3kn0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC02BFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC03NX0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC02BRC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC05XSTEPC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC02F0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC03PSSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC04planC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC05regs0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3seg;BndP_Na_101>LibSegNa_qtwC03kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qthJ.
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
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11$12$13$14+$32#60$21+$32#120$18$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40)$21##20$2:##20!$21#,1$2>'$2>##??!$2:#,1$30'$30##??'$2?##1'$26##??!$32#120,1#!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000!$2-118,8$32!$2-138,8$2?!$2-100,8$2:!$2-108,8+$32#20!$2-120,8&9$26#2"%pstring).
Definition ss0 : sym_state := SS 818836 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (36), ELit 4); ((EVar 33), (0), ELit 1); ((EVar 42), (0), ELit 1)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (36), 4); ((EVar 33), (0), 1); ((EVar 42), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,=#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<84><#<84><#5=#<84><,20#$1+$2-160$3$4$5$6$7$8+$2-160$2:&8&9$30#?=&9$26#2&9$26#2$=$>$?$10$11+&6$32#3#7???8000#7???8000+$32#20+$32#60$21+$32#120$32$19$1:$32$1<$1=$1>$1?,,2>!$2:#,1&8&9$30#?=&9$26#2!$21#,1&8&9$2>#?=@#2$2?!&6$32#3#7???8027,1^#?#??????????????8!&6$32#3#7???8026,1^#?#??????????????8!&6$32#3#7???8025,1^#?#??????????????8!&6$32#3#7???8024,1^#?#??????????????8'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-160#170$21##20)$21##20$32##200)$21##20$33##1)&6$21#3#7???8000#4&6$32#3#7???8000#40'$2:#6;6000#7?????????>0&$2:#8)##7???7000#100000001000$2:##20#&6$2:#3#7???8000#4($2:##20)$2-160#170$2:##20)$2:##20$32##200)$2:##20$33##1)&6$2:#3#7???8000#4&6$32#3#7???8000#40)$21##20$2:##20'$2>##??'$30##??'$2?##1'$26##??!$32#120,1#!$2-<8,8#7???8000!$2-?0,8+&6$32#3#7???8000!$2-118,8$32!$2-138,8$2?!$2-100,8$2:!$2-108,8+$32#20!$2-120,8&9$26#2,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 818836 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 818836 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthJ.

Module LibSegNa_qthPd.
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
Definition ss0 : sym_state := SS 820460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 820460 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 820460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthPd.

Module LibSegNa_qthX.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [534580].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$13+$32#20+$32#60$16$17$32$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#60,1&9$2<#?='$2<##??'&9$2<#1##!$32#20,1&9$2;#?='$2;##??'&9$2;#1##"%pstring).
Definition ss0 : sym_state := SS 820460 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 4); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), ELit 4); ((EVar 50), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 4); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), 4); ((EVar 50), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#82834#5=#82834,20##<856<+$2-160$3$4$5$6$7$8+$2-160+&6$32#3#7???8000#40$<$=$>$?$10$11+&6$32#3#7???8000^#?#??????????????8+$32#20+$32#60$16$17$32$19$1:$32$1<$1=$1>$1?,,18!$32#,8#45>0360>!&6$32#3#7???8007,1^#?#??????????????8!&6$32#3#7???8006,1^#?#??????????????8!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8!&6$32#3#7???800?,1^#?#??????????????8!&6$32#3#7???800>,1^#?#??????????????8!&6$32#3#7???800=,1^#?#??????????????8!&6$32#3#7???800<,1^#?#??????????????8'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#60,1&9$2<#?='$2<##??'&9$2<#1##!$32#20,1&9$2;#?='$2;##??'&9$2;#1##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 534580 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 820460 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 820460 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthX.

Module LibSegNa_qthXd.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [534580].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$8+$2-160$:$;$<$=$>$?$10$11+&6$32#3#7???8000$13+$32#20+$32#60$16$17$32$19$1:$32$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",<'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#20,1&9$2;#?='$2;##??'&9$2;#1##"%pstring).
Definition ss0 : sym_state := SS 820492 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), ELit 4); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), ELit 4); ((EVar 50), (0), ELit 8)].
Definition F0L : list SR.region := [((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (12), 4); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (4), 4); ((EVar 50), (0), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#82834#5=#82834,20##<856<+$2-160$3$4$5$6$7$8+$2-160+&6$32#3#7???8000#40$<$=$>$?$10$11+&6$32#3#7???8000^#?#??????????????8+$32#20+$32#60$16$17$32$19$1:$32$1<$1=$1>$1?,,15!$32#,8#45>0360>!&6$32#3#7???8007,1^#?#??????????????8!&6$32#3#7???8006,1^#?#??????????????8!&6$32#3#7???8005,1^#?#??????????????8!&6$32#3#7???8004,1^#?#??????????????8!&6$32#3#7???800?,1^#?#??????????????8!&6$32#3#7???800>,1^#?#??????????????8!&6$32#3#7???800=,1^#?#??????????????8!&6$32#3#7???800<,1^#?#??????????????8'$2#7???7?801160#800000000000&$2#20($2-160#160'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#20,1&9$2;#?='$2;##??'&9$2;#1##,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 534580 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 820492 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 820492 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthXd.

Module LibSegNa_qthZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_44d410.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_44d410.IT.
Definition ENDS : list Z := [820868].
Definition STOPS1 : list Z := [838104; 836056; 827044; 520280; 534580; 820868; 820872; 817696; 818988; 819080; 991168] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-160$3$4$5$6$7$34$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$32$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#1?8,8$33'$33#1000#7???????????($33##1)##7???7000#100000001000$33##1)$32##200$33##1)$2-160#170$33##1'$34#7???7?801160#800000000000&$34#10!$34-8,8$35!$34-10,8$36!$34-18,8$37!$34-20,8$38!$34-28,8$39!$34-30,8$3:!$34-38,8$3;!$34-40,8$3<!$34-48,8$3=!$34-50,8$3>!$34-58,8$3?!$34-60,8$40!$34-68,8$41)+$34-160##160$32##200)+$34-160##160$33##1"%pstring).
Definition ss0 : sym_state := SS 820588 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 51), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 51), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,<#<<9=8#<<1=8#<9>:4#7?058#82834#<8684#<8688#<7:20#<7?2<#<7?88#?1?<0#<8684#5=#<8684,20#$35$34$3$4$5$6$7$36$37$33$;$<$=$>$?$10$11$38$39$3:$3;$3<$3=$3>$3?$40$41$1<$1=$1>$1?,,1>!$33#,1#'$32#6;6000#7????????>00&$32#20)##7???7000#100000001000$32##200($32##200(&6$32#3#7???8000#40)$2-160#170$32##200!$32#1?8,8$33'$33#1000#7???????????($33##1)##7???7000#100000001000$33##1)$32##200$33##1)$2-160#170$33##1'$34#7???7?801160#800000000000&$34#10!$34-8,8$35!$34-10,8$36!$34-18,8$37!$34-20,8$38!$34-28,8$39!$34-30,8$3:!$34-38,8$3;!$34-40,8$3<!$34-48,8$3=!$34-50,8$3>!$34-58,8$3?!$34-60,8$40!$34-68,8$41)+$34-160##160$32##200)+$34-160##160$33##1,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 820868 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_44d410.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 820588 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_44d410.IT BndT_Na_001.SegItab_Na_44d410.IT_sound BF NX0 BR XSTEP F0 PSS plan 820588 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qthZ.

Module LibSegNa_qtmA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e24eef.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e24eef.IT.
Definition ENDS : list Z := [827428].
Definition STOPS1 : list Z := [827428] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",12%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-40#40$21##20!$21#,1$26'$26##??'&9$26#1##!$21#8,8$23!$21#10,8$24'$23##1"%pstring).
Definition ss0 : sym_state := SS 839180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-56), ELit 56)].
Definition F0L : list SR.region := [((EVar 2), (-56), 56)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<:024#<:024#5=#<:024,20##<<>;4+$2-40$3$4$5$6$7$21$22$21+$23#1#$=$>$?$10$11#7???8000$23$24+&6$21#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,19!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801040#800000000000&$2#10($2-40#40'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-40#40$21##20!$21#,1$26'$26##??'&9$26#1##!$21#8,8$23!$21#10,8$24'$23##1,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e24eef.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 839180 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e24eef.IT BndT_Na_003.SegItab_Na_e24eef.IT_sound BF NX0 BR XSTEP F0 PSS plan 839180 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtmA.

Module LibSegNa_qtmB0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e24eef.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e24eef.IT.
Definition ENDS : list Z := [830872].
Definition STOPS1 : list Z := [830872] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$21$22$:$;$<$=$>$?$10$11#7???8000#$24+&6$21#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",8'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##"%pstring).
Definition ss0 : sym_state := SS 839348 regs0 [] kn0 NX0.
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<:=98#<:=98#5=#<:=98,20##<<?<<$2$3$4#$6$7$21$22$21#$<$=$>$?$10$11#7???8000#$24+&6$21#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,9!$21#10,8#'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e24eef.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 839348 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e24eef.IT BndT_Na_003.SegItab_Na_e24eef.IT_sound BF NX0 BR XSTEP F0 PSS plan 839348 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtmB0.

Module LibSegNa_qtmB1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e24eef.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e24eef.IT.
Definition ENDS : list Z := [830872].
Definition STOPS1 : list Z := [830872] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$21$22$:$;$<$=$>$?$10$11#7???8000#1$24+&6$21#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",:'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##!$21#10,8$24!$21#18,8#"%pstring).
Definition ss0 : sym_state := SS 839348 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (16), ELit 16)].
Definition F0L : list SR.region := [((EVar 33), (16), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<:=98#<:=98#5=#<:=98,20##<<?<<$2$3$4+&4+@#100000000@&6$24#20&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20+&4+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20@#100000000@&9$24#????????&6$22#20+&6@&6$24#20&6@#100000000$22#20#20+&6@&9$24#????????&6$22#20#20@&6$24#20&6$22#20+$21#18&4+@#100000000@&6$24#20&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20$21#$21#&6$22#20+$21#20#????????&6@#100000000$22#20+&6+$21#10#3#7???8001##7???8000#1#+&6$21#3#7???8000$16$17$18$19$1:$1;+@#100000000@&6$24#20&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20&4+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20@#100000000@&9$24#????????&6$22#20&6@&6$24#20&6@#100000000$22#20#20&6@&9$24#????????&6$22#20#20,,:!$21#18,8+&4+@#100000000@&6$24#20&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20+&4+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20@#100000000@&9$24#????????&6$22#20+&6@&6$24#20&6@#100000000$22#20#20+&6@&9$24#????????&6$22#20#20@&6$24#20&6$22#20!$21#10,8+@#100000000@&6$24#20&6@#100000000$22#20+@#100000000@&9$24#????????&6$22#20@&9$24#????????&6@#100000000$22#20'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20!$21#,1$26'$26##??'&9$26#1##,50!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e24eef.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 839348 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e24eef.IT BndT_Na_003.SegItab_Na_e24eef.IT_sound BF NX0 BR XSTEP F0 PSS plan 839348 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtmB1.

Module LibSegNa_qtmC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_003.SegItab_Na_e24eef.ITR.
Definition IT : itab := BndT_Na_003.SegItab_Na_e24eef.IT.
Definition ENDS : list Z := [839664].
Definition STOPS1 : list Z := [839664] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-40$3$4$5$6$7$21$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?801040#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37!$2-20,8$38!$2-28,8$39!$2-30,8$3:!$2-38,8$3;"%pstring).
Definition ss0 : sym_state := SS 839628 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<<??0#<<??0#5=#<<??0,20#$35$2$3$4$5$6$7$36$37$21$;$<$=$>$?$10$11$38$39$3:$3;$16$17$18$19$1:$1;$1<$1=$1>$1?,,9'$2#7???7?801040#800000000000&$2#10!$2-8,8$35!$2-10,8$36!$2-18,8$37!$2-20,8$38!$2-28,8$39!$2-30,8$3:!$2-38,8$3;,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 839664 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_003.SegItab_Na_e24eef.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 839628 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_003.SegItab_Na_e24eef.IT BndT_Na_003.SegItab_Na_e24eef.IT_sound BF NX0 BR XSTEP F0 PSS plan 839628 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtmC.

Module LibSegNa_qtvI.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_8edc8b.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_8edc8b.IT.
Definition ENDS : list Z := [828944].
Definition STOPS1 : list Z := [828944; 828948; 828560] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 34); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",10%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801070#800000000000&$2#10($2-70#70'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-70#70$21##20!$21#,1$26'$26##??'&9$26#1##'$22##2"%pstring).
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

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,4#<:610#<:614#<:490#<:610#5=#<:610,20#$1$2$3$4$5$6$7$8$9#3$22#15?:78$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1=!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?801070#800000000000&$2#10($2-70#70'$21#6;6000#7?????????>0&$21#8)##7???7000#100000001000$21##20#&6$21#3#7???8000#4($21##20)$2-70#70$21##20!$21#,1$26'$26##??'&9$26#1##'$22##2,50!"%pstring).
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
End LibSegNa_qtvI.

Module LibSegNa_qtwA0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [412400].
Definition STOPS1 : list Z := [412400; 867724] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; (EVar 33); (EVar 45); EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487392 140737488355328;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-224)) (ELit 224)].
Definition ss0 : sym_state := SS 867600 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-224), ELit 224)].
Definition F0L : list SR.region := [((EVar 2), (-224), 224)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64:?0#=3=8<#64:?0#5=#64:?0,20##=3=84+$2->0$3$4$5$6$7$2+$2->0#:0#15?:78#1$=$>$?$10$11$12$13$2=#7???8000$16$17$18$21$1:$1;$1<$1=$1>$1?,,14!$2-68,8$1;!$2-60,8$1:!$2-58,8$19!$2-50,8$18!$2-48,8$17!$2-40,8$16!$2-38,8$15!$2-30,8$14!$2-28,8$13!$2-20,8$12!$2-18,8$9!$2-10,8$8!$2-8,8$1!$2->0,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010>0#800000000000&$2#20($2->0#>0,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 412400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867600 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwA0.

Module LibSegNa_qtwA16.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [412400].
Definition STOPS1 : list Z := [412400; 867724] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2#10$3$4$5$6$7$8$9$21$2=$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KImg 65536 1409024;
   KWord (SA (ELit 0) 1440376) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1440384) 4 (ELit 1);
   KRange (EVar 2) 140735332487392 140737488355312;
   KAlign (EVar 2) 32;
   KWr (SA (EVar 2) (-224)) (ELit 240)].
Definition ss0 : sym_state := SS 867600 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-208), ELit 224)].
Definition F0L : list SR.region := [((EVar 2), (-208), 224)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,3#64:?0#=3=8<#64:?0#5=#64:?0,20##=3=84+$2->0$3$4$5$6$7+$2#10+$2->0#:0#15?:78#1$=$>$?$10$11$12$13$2=#7???8000$16$17$18$21$1:$1;$1<$1=$1>$1?,,14!$2-58,8$1;!$2-50,8$1:!$2-48,8$19!$2-40,8$18!$2-38,8$17!$2-30,8$16!$2-28,8$15!$2-20,8$14!$2-18,8$13!$2-10,8$12!$2-8,8$9!$2#,8$8!$2#8,8$1!$2-=0,8#%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1'$2#7???7?8010>0#7??????????0&$2#20($2->0#?0,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 412400 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867600 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867600 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwA16.

Module LibSegNa_qtwB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [833184].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$32$;$<$=$>$?$10$11$12$13$2=#7???8000$16$17$18$21$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",9'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100"%pstring).
Definition ss0 : sym_state := SS 867716 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-144), ELit 8); ((EVar 50), (0), ELit 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), ELit 20)].
Definition F0L : list SR.region := [((EVar 2), (-144), 8); ((EVar 50), (0), 24); ((EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 50) (ELit 3)) (ELit (2147450880))), (0), 20)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#<;6:0#5=#<;6:0,20##=3>54+$2->0$3$4$5$6$7$8+$2->0+$32#20$21#=3=10&6$32#3$>$?$10$11$12+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?,,21!&6$32#3#7???8007,1#!&6$32#3#7???8006,1#!&6$32#3#7???8005,1#!&6$32#3#7???8004,1#!&6$32#3#7???8013,1^#?#??????????????3!&6$32#3#7???8012,1^#?#??????????????3!&6$32#3#7???8011,1^#?#??????????????3!&6$32#3#7???8010,1^#?#??????????????3!&6$32#3#7???800;,1^#?#??????????????2!&6$32#3#7???800:,1^#?#??????????????2!&6$32#3#7???8009,1^#?#??????????????2!&6$32#3#7???8008,1^#?#??????????????2!&6$32#3#7???800?,1^#?#??????????????8!&6$32#3#7???800>,1^#?#??????????????8!&6$32#3#7???800=,1^#?#??????????????8!&6$32#3#7???800<,1^#?#??????????????8!&6$32#3#7???8003,1^#?#??????????????1!&6$32#3#7???8002,1^#?#??????????????1!&6$32#3#7???8001,1^#?#??????????????1!&6$32#3#7???8000,1^#?#??????????????1!$32#10,8#=3=10!$32#8,8#1;938!$32#,8#41;58:;3!$2-90,8$32'$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 833184 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867716 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867716 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwB.

Module LibSegNa_qtwC0.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_002.SegItab_Na_b3c509.ITR.
Definition IT : itab := BndT_Na_002.SegItab_Na_b3c509.IT.
Definition ENDS : list Z := [999896].
Definition STOPS1 : list Z := [833184; 999896; 1001024; 520280; 817564; 868976; 867724; 991168; 868980; 868992; 869008; 869012; 869016; 869020] ++ ENDS.
Definition NX0 : nat := 80.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2->0$3$4$5$6$7$8+$2->0$:$;$<$=$>$?$10$11$12+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",='$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1!$32#28,8#"%pstring).
Definition ss0 : sym_state := SS 867924 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,?#<;6:0#?41=8#?4640#7?058#<799<#=4270#=3=8<#?1?<0#=4274#=4280#=4290#=4294#=4298#=429<#?41=8#5=#?41=8,20##=3>78+$2->0$3$4$5$6$7$8+$2->0$2=#2$<$=$>$?$10$11#+&6$32#3#7???8000$2=#7???8000$32$32+$32#20$21$1:$1;$1<$1=$1>$1?,,='$2#7???7?8010>0#800000000000&$2#20($2->0#>0'$32#6;6000#7?????????00&$32#20)##7???7000#100000001000$32##100($32##100(&6$32#3#7???8000#20)$2->0#?0$32##100%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1!$32#28,8#,50!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 999896 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_002.SegItab_Na_b3c509.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 867924 regs0 kn0 = true.
Proof. apply Mh_0128.SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

Definition seg_sound_ax := as0_plan_sound_it BndT_Na_002.SegItab_Na_b3c509.IT BndT_Na_002.SegItab_Na_b3c509.IT_sound BF NX0 BR XSTEP F0 PSS plan 867924 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
End LibSegNa_qtwC0.
