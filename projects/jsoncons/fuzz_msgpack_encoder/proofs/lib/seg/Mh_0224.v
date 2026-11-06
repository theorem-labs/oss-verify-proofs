(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0099. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require asan.XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_000. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module BndP_Na_143.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0099. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require asan.XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0099.SegPlanAutoX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001 BndT_Na_000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_143 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_by_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_404c852ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh2BRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F7xstep_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAh3kn0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS05xstepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F:xstep_f_eqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_aicAl3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_000ASegItab_Na_28237f2ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143=LibSegNa_aliA3kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_4022922ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAh3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_143>LibSegNa_qpcAl3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_aicAh.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [1172152].
Definition STOPS1 : list Z := [1172152; 519088; 519096] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#10007???8040#7????????>>7&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!##156=98,8#15?:78!##15?:78,8#7???8000!##156=:0,8#160768!##160768,8#!##156=:8,8#160770!##160770,8#!##156=;0,8#160760!##160760,8#7???????????!##157900,8#160759!##160759,1#1!##158=:8,8#14916<!##158=:0,8#148=68###80022938#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 719888 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(519088, 0%nat); (519096, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152])], (93, SS 1172152 [ELit 0; ELit 720224; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1395272; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1395248; ELit 2147450880; ELit 1395184; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 720224); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1395360); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1395320); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1376256 1409024; KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1440384 |} 4 (ELit 1); KRange (EVar 33) 17594333495360 140737488355047; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1404312 |} 8 (ELit 1440376); KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1404320 |} 8 (ELit 1443688); KWord {| a_base := ELit 0; a_off := 1443688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404328 |} 8 (ELit 1443696); KWord {| a_base := ELit 0; a_off := 1443696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404336 |} 8 (ELit 1443680); KWord {| a_base := ELit 0; a_off := 1443680 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1407232 |} 8 (ELit 1443673); KWord {| a_base := ELit 0; a_off := 1443673 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1412520 |} 8 (ELit 1347948); KWord {| a_base := ELit 0; a_off := 1412512 |} 8 (ELit 1346920); KZero {| a_base := ELit 0; a_off := 2147625272 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 1172152 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 719888 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 719888 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicAh.

Module LibSegNa_aicAl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [1172152].
Definition STOPS1 : list Z := [1172152; 519088; 519096] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-40#8$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",1='$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7???6>?0&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!##156=98,8#15?:78!##15?:78,8#7???8000!##156=:0,8#160768!##160768,8#!##156=:8,8#160770!##160770,8#!##156=;0,8#160760!##160760,8#7???????????!##157900,8#160759!##160759,1#1!##158=:8,8#14916<!##158=:0,8#148=68###80022938#20#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 719888 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 16); ((EVar 33), (120), ELit 136)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 16); ((EVar 33), (120), 136)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(519088, 0%nat); (519096, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152])], (93, SS 1172152 [ELit 0; ELit 720224; EAlu Instr.ALU_ADD (EVar 2) (ELit (-112)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EVar 33; EAlu Instr.ALU_ADD (EVar 33) (ELit 168); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; ELit 8; EAlu Instr.ALU_ADD (EVar 33) (ELit (-64)); ELit 1395272; EAlu Instr.ALU_ADD (EVar 33) (ELit 16); EAlu Instr.ALU_ADD (EVar 33) (ELit 120); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)) (ELit 3)) (ELit 2147450880); ELit 1395248; ELit 2147450880; ELit 1395184; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880); EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 176 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 152 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 144 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 128 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 16)); KWord {| a_base := EVar 33; a_off := 156 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 120)); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 720224); KWord {| a_base := EVar 33; a_off := 8 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 120 |} 8 (ELit 1395360); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1395320); KWord {| a_base := EVar 33; a_off := 168 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1376256 1409024; KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1440384 |} 4 (ELit 1); KRange (EVar 33) 7036992 2147446512; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 34); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EVar 33; a_off := 0 |} (ELit 272); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EVar 33; a_off := -64 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1404312 |} 8 (ELit 1440376); KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1404320 |} 8 (ELit 1443688); KWord {| a_base := ELit 0; a_off := 1443688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404328 |} 8 (ELit 1443696); KWord {| a_base := ELit 0; a_off := 1443696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404336 |} 8 (ELit 1443680); KWord {| a_base := ELit 0; a_off := 1443680 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1407232 |} 8 (ELit 1443673); KWord {| a_base := ELit 0; a_off := 1443673 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1412520 |} 8 (ELit 1347948); KWord {| a_base := ELit 0; a_off := 1412512 |} 8 (ELit 1346920); KZero {| a_base := ELit 0; a_off := 2147625272 |} (ELit 32); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 1172152 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 719888 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 719888 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicAl.

Module LibSegNa_aliA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_000.SegItab_Na_28237f.ITR.
Definition IT : itab := BndT_Na_000.SegItab_Na_28237f.IT.
Definition ENDS : list Z := [1172244].
Definition STOPS1 : list Z := [1172244; 519088] ++ ENDS.
Definition NX0 : nat := 48.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 33; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",26'$2#7???7?802000#800000000000&$2#10($2-1000#1000'$21#6;6000#7??????????8&$21#8)##7???7000#100000001000$21##8)$2-1000#1000$21##8($21##8%#10000#158000!##15?:78,8#7???8000!##15?:80,4#1%#692332#692:70(##692332#73>%#693198#6931?0(##693198#58!##6;3=93,1#!##6;3>70,4#!##6;3;40,8$22!##156=98,8#15?:78!##15?:78,8#7???8000!##156=:0,8#160768!##160768,8#!##156=:8,8#160770!##160770,8#!##156=;0,8#160760!##160760,8#7???????????!##157900,8#160759!##160759,1#1!##158=:8,8#14916<!##158=:0,8#148=68!##160758,1#1!##158;=0,8#148=38!##1?16:6,1#1!##1?16:7,1#1###800<:45>#?8###800<:62;#1;###7???===9#41#&6$2#3#7???7>00#200"%pstring).
Definition ss0 : sym_state := SS 1172152 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 8); ((ELit 0), (6890290), ELit 1854); ((ELit 0), (6893976), ELit 88)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 8); ((ELit 0), (6890290), 1854); ((ELit 0), (6893976), 88)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(519088, 0%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172244; 519088; 1172244])], (93, SS 1172244 [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 529; EVar 530; EVar 531; EVar 8; EVar 9; ELit 6891840; ELit 6891840; EVar 534; EVar 535; EVar 536; EVar 537; EVar 538; EVar 539; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 540; EVar 541; EVar 542; EVar 543] [] [KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 6891840); KWord {| a_base := ELit 0; a_off := 6890801 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890800 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890792 |} 8 (ELit 6891840); KWord {| a_base := ELit 0; a_off := 6890785 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890784 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890776 |} 8 (ELit 6891840); KWord {| a_base := ELit 0; a_off := 6892112 |} 8 (ELit 6891384); KWord {| a_base := ELit 0; a_off := 6891864 |} 8 (ELit 6892120); KWord {| a_base := EVar 2; a_off := -272 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -264 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -256 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -248 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 6891392); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 29); KWord {| a_base := EVar 2; a_off := -224 |} 8 (ELit 6891840); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 6891856); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 6891384); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 1145992); KWord {| a_base := ELit 0; a_off := 6891392 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6894048 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6894056 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6894024 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6893980 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 6890608 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890616 |} 4 (ELit 30); KWord {| a_base := ELit 0; a_off := 6890624 |} 4 (ELit 30); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-168))); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EAlu Instr.ALU_ADD (EVar 2) (ELit (-184))); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 6890608); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -152 |} 8 (ELit 6890760); KWord {| a_base := EVar 2; a_off := -144 |} 8 (ELit 6890768); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 1396344); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 6891840); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 1136104); KWord {| a_base := ELit 0; a_off := 6891384 |} 8 (ELit 1402416); KWord {| a_base := ELit 0; a_off := 6892104 |} 8 (ELit 6891368); KWord {| a_base := ELit 0; a_off := 6891376 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890592 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890600 |} 4 (ELit 29); KWord {| a_base := ELit 0; a_off := 6891368 |} 8 (ELit 1402280); KWord {| a_base := ELit 0; a_off := 6892096 |} 8 (ELit 6891592); KWord {| a_base := ELit 0; a_off := 6891600 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890448 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890456 |} 4 (ELit 28); KWord {| a_base := ELit 0; a_off := 6891608 |} 8 (ELit 192360); KWord {| a_base := ELit 0; a_off := 6891592 |} 8 (ELit 1400288); KWord {| a_base := ELit 0; a_off := 6892088 |} 8 (ELit 6891568); KWord {| a_base := ELit 0; a_off := 6891576 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890432 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890440 |} 4 (ELit 27); KWord {| a_base := ELit 0; a_off := 6891584 |} 8 (ELit 192360); KWord {| a_base := ELit 0; a_off := 6891568 |} 8 (ELit 1400168); KWord {| a_base := ELit 0; a_off := 6892080 |} 8 (ELit 6891544); KWord {| a_base := ELit 0; a_off := 6891552 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890416 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890424 |} 4 (ELit 26); KWord {| a_base := ELit 0; a_off := 6891560 |} 8 (ELit 1399384); KWord {| a_base := ELit 0; a_off := 6891544 |} 8 (ELit 1399288); KWord {| a_base := ELit 0; a_off := 6892072 |} 8 (ELit 6891520); KWord {| a_base := ELit 0; a_off := 6891528 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890400 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890408 |} 4 (ELit 25); KWord {| a_base := ELit 0; a_off := 6891536 |} 8 (ELit 1399112); KWord {| a_base := ELit 0; a_off := 6891520 |} 8 (ELit 1399016); KWord {| a_base := ELit 0; a_off := 6892064 |} 8 (ELit 6891352); KWord {| a_base := ELit 0; a_off := 6891360 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890576 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890584 |} 4 (ELit 24); KWord {| a_base := ELit 0; a_off := 6891352 |} 8 (ELit 1402152); KWord {| a_base := ELit 0; a_off := 6892056 |} 8 (ELit 6891336); KWord {| a_base := ELit 0; a_off := 6891344 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890560 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890568 |} 4 (ELit 23); KWord {| a_base := ELit 0; a_off := 6891336 |} 8 (ELit 1402024); KWord {| a_base := ELit 0; a_off := 6892048 |} 8 (ELit 6891320); KWord {| a_base := ELit 0; a_off := 6891328 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890544 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890552 |} 4 (ELit 22); KWord {| a_base := ELit 0; a_off := 6891320 |} 8 (ELit 1401896); KWord {| a_base := ELit 0; a_off := 6892040 |} 8 (ELit 6891304); KWord {| a_base := ELit 0; a_off := 6891312 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890528 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890536 |} 4 (ELit 21); KWord {| a_base := ELit 0; a_off := 6891304 |} 8 (ELit 1401768); KWord {| a_base := ELit 0; a_off := 6892032 |} 8 (ELit 6891288); KWord {| a_base := ELit 0; a_off := 6891296 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890512 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890520 |} 4 (ELit 20); KWord {| a_base := ELit 0; a_off := 6891288 |} 8 (ELit 1401056); KWord {| a_base := ELit 0; a_off := 6892024 |} 8 (ELit 6891272); KWord {| a_base := ELit 0; a_off := 6891280 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890496 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890504 |} 4 (ELit 19); KWord {| a_base := ELit 0; a_off := 6891272 |} 8 (ELit 1400888); KWord {| a_base := ELit 0; a_off := 6892016 |} 8 (ELit 6891256); KWord {| a_base := ELit 0; a_off := 6891264 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890480 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890488 |} 4 (ELit 18); KWord {| a_base := ELit 0; a_off := 6891256 |} 8 (ELit 1400720); KWord {| a_base := ELit 0; a_off := 6892008 |} 8 (ELit 6891240); KWord {| a_base := ELit 0; a_off := 6891248 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890464 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890472 |} 4 (ELit 17); KWord {| a_base := ELit 0; a_off := 6891240 |} 8 (ELit 1400536); KWord {| a_base := ELit 0; a_off := 6892000 |} 8 (ELit 6891224); KWord {| a_base := ELit 0; a_off := 6891232 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890384 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890392 |} 4 (ELit 16); KWord {| a_base := ELit 0; a_off := 6891224 |} 8 (ELit 1398816); KWord {| a_base := ELit 0; a_off := 6891992 |} 8 (ELit 6891208); KWord {| a_base := ELit 0; a_off := 6891216 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890368 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890376 |} 4 (ELit 15); KWord {| a_base := ELit 0; a_off := 6891208 |} 8 (ELit 1398600); KWord {| a_base := ELit 0; a_off := 6891984 |} 8 (ELit 6891192); KWord {| a_base := ELit 0; a_off := 6891200 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890352 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890360 |} 4 (ELit 14); KWord {| a_base := ELit 0; a_off := 6891192 |} 8 (ELit 1398376); KWord {| a_base := ELit 0; a_off := 6891976 |} 8 (ELit 6891176); KWord {| a_base := ELit 0; a_off := 6891184 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890336 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890344 |} 4 (ELit 13); KWord {| a_base := ELit 0; a_off := 6891176 |} 8 (ELit 1398136); KWord {| a_base := ELit 0; a_off := 6891968 |} 8 (ELit 6891792); KWord {| a_base := ELit 0; a_off := 6891800 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6891032 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6891040 |} 4 (ELit 12); KWord {| a_base := ELit 0; a_off := 6891832 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891824 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891816 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891808 |} 8 (ELit 188978561070); KWord {| a_base := ELit 0; a_off := 6891792 |} 8 (ELit 1396104); KWord {| a_base := ELit 0; a_off := 6891960 |} 8 (ELit 6891744); KWord {| a_base := ELit 0; a_off := 6891752 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6891016 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6891024 |} 4 (ELit 11); KWord {| a_base := ELit 0; a_off := 6891784 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891776 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891768 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891760 |} 2 (ELit 11310); KWord {| a_base := ELit 0; a_off := 6891744 |} 8 (ELit 1396024); KWord {| a_base := ELit 0; a_off := 6891952 |} 8 (ELit 6891160); KWord {| a_base := ELit 0; a_off := 6891168 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890712 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890720 |} 4 (ELit 10); KWord {| a_base := ELit 0; a_off := 6891160 |} 8 (ELit 1397240); KWord {| a_base := ELit 0; a_off := 6891944 |} 8 (ELit 6891144); KWord {| a_base := ELit 0; a_off := 6891152 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890680 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890688 |} 4 (ELit 9); KWord {| a_base := ELit 0; a_off := 6891144 |} 8 (ELit 1396936); KWord {| a_base := ELit 0; a_off := 6891936 |} 8 (ELit 6891128); KWord {| a_base := ELit 0; a_off := 6891136 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890696 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890704 |} 4 (ELit 8); KWord {| a_base := ELit 0; a_off := 6891128 |} 8 (ELit 1397088); KWord {| a_base := ELit 0; a_off := 6891928 |} 8 (ELit 6891112); KWord {| a_base := ELit 0; a_off := 6891120 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890664 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890672 |} 4 (ELit 7); KWord {| a_base := ELit 0; a_off := 6891112 |} 8 (ELit 1396784); KWord {| a_base := ELit 0; a_off := 6891920 |} 8 (ELit 6891496); KWord {| a_base := ELit 0; a_off := 6891504 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890648 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890656 |} 4 (ELit 6); KWord {| a_base := ELit 0; a_off := 6891512 |} 8 (ELit 192360); KWord {| a_base := ELit 0; a_off := 6890769 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890768 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890760 |} 8 (ELit 192360); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891496 |} 8 (ELit 1395928); KWord {| a_base := ELit 0; a_off := 6891912 |} 8 (ELit 6891096); KWord {| a_base := ELit 0; a_off := 6891104 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890632 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890640 |} 4 (ELit 5); KWord {| a_base := ELit 0; a_off := 6891096 |} 8 (ELit 1396616); KWord {| a_base := ELit 0; a_off := 6891904 |} 8 (ELit 6891080); KWord {| a_base := ELit 0; a_off := 6891088 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890984 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890992 |} 4 (ELit 4); KWord {| a_base := ELit 0; a_off := 6891080 |} 8 (ELit 1396408); KWord {| a_base := ELit 0; a_off := 6891896 |} 8 (ELit 6891616); KWord {| a_base := ELit 0; a_off := 6891624 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6891000 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6891008 |} 4 (ELit 3); KWord {| a_base := ELit 0; a_off := 6891640 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891632 |} 8 (ELit 170360); KWord {| a_base := ELit 0; a_off := 6891616 |} 8 (ELit 1395584); KWord {| a_base := ELit 0; a_off := 6891888 |} 8 (ELit 6891064); KWord {| a_base := ELit 0; a_off := 6891072 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890320 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890328 |} 4 (ELit 2); KWord {| a_base := ELit 0; a_off := 6891064 |} 8 (ELit 1398072); KWord {| a_base := ELit 0; a_off := 6891880 |} 8 (ELit 6891048); KWord {| a_base := ELit 0; a_off := 6891056 |} 8 (ELit 1); KWord {| a_base := ELit 0; a_off := 6890304 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6890312 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 6891048 |} 8 (ELit 1398008); KWord {| a_base := ELit 0; a_off := 6892130 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6892128 |} 2 (ELit 17154); KWord {| a_base := ELit 0; a_off := 6891872 |} 8 (ELit 6892120); KWord {| a_base := ELit 0; a_off := 6891856 |} 8 (ELit 6891880); KWord {| a_base := ELit 0; a_off := 6891848 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6891840 |} 8 (ELit 1395416); KWord {| a_base := ELit 0; a_off := 6892120 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -96 |} 8 (ELit 6890760); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 6891840); KWord {| a_base := EVar 2; a_off := -80 |} 8 (ELit 6890784); KWord {| a_base := EVar 2; a_off := -72 |} 8 (ELit 1148172); KWord {| a_base := EVar 2; a_off := -64 |} 8 (ELit 6890760); KWord {| a_base := EVar 2; a_off := -56 |} 8 (ELit 6890800); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 1172272); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KRange (EVar 33) 7036928 140737488355320; KAlign (EVar 33) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 33; a_off := 0 |} (ELit 8); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 33; a_off := 0 |} (ELit 8); KWr {| a_base := EVar 33; a_off := 0 |} (ELit 8); KImg 65536 1409024; KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1440384 |} 4 (ELit 1); KImg 6890290 6890304; KImg 6890316 6890320; KImg 6890332 6890336; KImg 6890348 6890352; KImg 6890364 6890368; KImg 6890380 6890384; KImg 6890396 6890400; KImg 6890412 6890416; KImg 6890428 6890432; KImg 6890444 6890448; KImg 6890460 6890464; KImg 6890476 6890480; KImg 6890492 6890496; KImg 6890508 6890512; KImg 6890524 6890528; KImg 6890540 6890544; KImg 6890556 6890560; KImg 6890572 6890576; KImg 6890588 6890592; KImg 6890604 6890608; KImg 6890620 6890624; KImg 6890628 6890632; KImg 6890644 6890648; KImg 6890660 6890664; KImg 6890676 6890680; KImg 6890692 6890696; KImg 6890708 6890712; KImg 6890724 6890760; KImg 6890770 6890776; KImg 6890786 6890792; KImg 6890802 6890984; KImg 6890996 6891000; KImg 6891012 6891016; KImg 6891028 6891032; KImg 6891044 6891048; KImg 6891400 6891496; KImg 6891641 6891744; KImg 6891762 6891768; KImg 6892131 6892144; KWr {| a_base := ELit 0; a_off := 6890290 |} (ELit 1854); KImg 6893976 6893980; KImg 6893984 6894024; KImg 6894032 6894048; KImg 6894052 6894056; KWr {| a_base := ELit 0; a_off := 6893976 |} (ELit 88); KWord {| a_base := ELit 0; a_off := 7028115 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 7028336 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 7027520 |} 8 (EVar 34); KWord {| a_base := ELit 0; a_off := 1404312 |} 8 (ELit 1440376); KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1404320 |} 8 (ELit 1443688); KWord {| a_base := ELit 0; a_off := 1443688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404328 |} 8 (ELit 1443696); KWord {| a_base := ELit 0; a_off := 1443696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404336 |} 8 (ELit 1443680); KWord {| a_base := ELit 0; a_off := 1443680 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1407232 |} 8 (ELit 1443673); KWord {| a_base := ELit 0; a_off := 1443673 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1412520 |} 8 (ELit 1347948); KWord {| a_base := ELit 0; a_off := 1412512 |} 8 (ELit 1346920); KWord {| a_base := ELit 0; a_off := 1443672 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1412048 |} 8 (ELit 1346872); KWord {| a_base := ELit 0; a_off := 2037414 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 2037415 |} 1 (ELit 1); KZero {| a_base := ELit 0; a_off := 2148312158 |} (ELit 248); KZero {| a_base := ELit 0; a_off := 2148312619 |} (ELit 27); KZero {| a_base := ELit 0; a_off := 2147474905 |} (ELit 65); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 2) (ELit 3); a_off := 2147450368 |} (ELit 512)] 544))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 1172244 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_000.SegItab_Na_28237f.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1172152 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_000.SegItab_Na_28237f.IT BndT_Na_000.SegItab_Na_28237f.IT_sound BF NX0 BR XSTEP F0 PSS plan 1172152 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aliA.

Module LibSegNa_qpcAh.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [1172152].
Definition STOPS1 : list Z := [1172152; 519088; 519096] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-1?0$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#10007???8000#7????????<77&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18!##156=98,8#15?:78!##15?:78,8#7???8000!##156=:0,8#160768!##160768,8#!##156=:8,8#160770!##160770,8#!##156=;0,8#160760!##160760,8#7???????????!##157900,8#160759!##160759,1#1!##158=:8,8#14916<!##158=:0,8#148=68###8002219:#40###80022938#20"%pstring).
Definition ss0 : sym_state := SS 846716 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 400)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 400)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(519088, 0%nat); (519096, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152])], (93, SS 1172152 [ELit 0; ELit 849248; EAlu Instr.ALU_ADD (EVar 2) (ELit (-192)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 48); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 112); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 849248); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1380600); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1380560); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -168 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 847912); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 34); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 846940); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1380328); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1376256 1409024; KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1440384 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 17594333495296 140737488354423; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 896); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 896); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 896); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) (ELit 3); a_off := 2147450880 |} (ELit 34); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 400); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 50); KRange (EVar 34) 7036928 140737488355296; KAlign (EVar 34) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 34) (ELit 3); a_off := 2147450880 |} (ELit 3); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 400) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1404312 |} 8 (ELit 1440376); KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1404320 |} 8 (ELit 1443688); KWord {| a_base := ELit 0; a_off := 1443688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404328 |} 8 (ELit 1443696); KWord {| a_base := ELit 0; a_off := 1443696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404336 |} 8 (ELit 1443680); KWord {| a_base := ELit 0; a_off := 1443680 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1407232 |} 8 (ELit 1443673); KWord {| a_base := ELit 0; a_off := 1443673 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1412520 |} 8 (ELit 1347948); KWord {| a_base := ELit 0; a_off := 1412512 |} 8 (ELit 1346920); KZero {| a_base := ELit 0; a_off := 2147623322 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147625272 |} (ELit 32)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 1172152 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 846716 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 846716 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcAh.

Module LibSegNa_qpcAl.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [1172152].
Definition STOPS1 : list Z := [1172152; 519088; 519096] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1$2$3$4$5$6$7$8$9$21+$21-1?0$22$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",24'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7???6<80&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18!##156=98,8#15?:78!##15?:78,8#7???8000!##156=:0,8#160768!##160768,8#!##156=:8,8#160770!##160770,8#!##156=;0,8#160760!##160760,8#7???????????!##157900,8#160759!##160759,1#1!##158=:8,8#14916<!##158=:0,8#148=68###8002219:#40###80022938#20"%pstring).
Definition ss0 : sym_state := SS 846716 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-4096), ELit 4096); ((EVar 33), (0), ELit 400)].
Definition F0L : list SR.region := [((EVar 2), (-4096), 4096); ((EVar 33), (0), 400)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition PXA : list (Z * nat) := [(519088, 0%nat); (519096, 1%nat)].
Definition AUTO := SGAX.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0 XSTEP PXA.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGAX.aitem * (Z * sym_state) :=
  (([SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152]); SGAX.APX 0; SGAX.AStep (SR.SBlock [1172152; 519088; 519096; 1172152])], (93, SS 1172152 [ELit 0; ELit 849248; EAlu Instr.ALU_ADD (EVar 2) (ELit (-192)); EVar 3; EVar 4; EVar 61; EVar 62; EVar 63; EAlu Instr.ALU_ADD (EVar 33) (ELit 32); EAlu Instr.ALU_ADD (EVar 33) (ELit 48); EAlu Instr.ALU_ADD (EVar 33) (ELit 160); EVar 65; EVar 66; EVar 67; EVar 68; EVar 69; EVar 70; EVar 71; EAlu Instr.ALU_ADD (EVar 33) (ELit 112); ELit 2147450880; EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)) (ELit 3)) (ELit 2147450880); EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit 112)) (ELit 3)) (ELit 2147450880); EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 72; EVar 73; EVar 74; EVar 75] [] [KZero {| a_base := EVar 33; a_off := 168 |} (ELit 80); KWord {| a_base := EVar 33; a_off := 144 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 136 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 128 |} 8 (ELit 6); KWord {| a_base := EVar 33; a_off := 120 |} 4 (ELit 4098); KWord {| a_base := EVar 33; a_off := 152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 48)); KWord {| a_base := EVar 33; a_off := 148 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 849248); KWord {| a_base := EVar 33; a_off := 40 |} 8 (ELit 0); KWord {| a_base := EVar 33; a_off := 112 |} 8 (ELit 1380600); KWord {| a_base := EVar 33; a_off := 32 |} 8 (ELit 1380560); KWord {| a_base := EVar 33; a_off := 160 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -184 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -168 |} 8 (ELit 2147450880); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 32)); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 847912); KWord {| a_base := EVar 2; a_off := -120 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -112 |} 8 (EVar 34); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EAlu Instr.ALU_ADD (EVar 33) (ELit 24)); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 33); KWord {| a_base := EVar 2; a_off := -88 |} 8 (ELit 846940); KWord {| a_base := EVar 33; a_off := 20 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 16 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 12 |} 4 (ELit 0); KWord {| a_base := EVar 33; a_off := 9 |} 1 (ELit 0); KWord {| a_base := EVar 33; a_off := 8 |} 1 (ELit 1); KWord {| a_base := EVar 33; a_off := 0 |} 8 (ELit 1380328); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -48 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -40 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -24 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (EVar 1); KRange (EVar 2) 140735332491264 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -4096 |} (ELit 4096); KImg 1376256 1409024; KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1440384 |} 4 (ELit 1); KRange (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 7036928 2147445888; KAlign (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 896); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 896); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EAlu Instr.ALU_ADD (EVar 33) (ELit (-496)); a_off := 0 |} (ELit 896); KZero {| a_base := EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 33) (ELit (-496))) (ELit 3); a_off := 2147450880 |} (ELit 34); KAlign (EVar 33) 8; KWr {| a_base := EVar 33; a_off := 0 |} (ELit 400); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 33) (ELit 3); a_off := 2147450880 |} (ELit 50); KRange (EVar 34) 7036928 140737488355296; KAlign (EVar 34) 8; KDisj {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KZero {| a_base := EAlu Instr.ALU_SRL (EVar 34) (ELit 3); a_off := 2147450880 |} (ELit 3); KDisj {| a_base := EVar 2; a_off := -4096 |} (ELit 4096) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KDisj {| a_base := ELit 0; a_off := 65536 |} (ELit 6971392) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KDisj {| a_base := EVar 33; a_off := 0 |} (ELit 400) {| a_base := EVar 34; a_off := 0 |} (ELit 24); KWord {| a_base := ELit 0; a_off := 1404312 |} 8 (ELit 1440376); KWord {| a_base := ELit 0; a_off := 1440376 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1404320 |} 8 (ELit 1443688); KWord {| a_base := ELit 0; a_off := 1443688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404328 |} 8 (ELit 1443696); KWord {| a_base := ELit 0; a_off := 1443696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1404336 |} 8 (ELit 1443680); KWord {| a_base := ELit 0; a_off := 1443680 |} 8 (ELit 140737488355327); KWord {| a_base := ELit 0; a_off := 1407232 |} 8 (ELit 1443673); KWord {| a_base := ELit 0; a_off := 1443673 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1412520 |} 8 (ELit 1347948); KWord {| a_base := ELit 0; a_off := 1412512 |} 8 (ELit 1346920); KZero {| a_base := ELit 0; a_off := 2147623322 |} (ELit 64); KZero {| a_base := ELit 0; a_off := 2147625272 |} (ELit 32)] 76))).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGAX.mkplan (fst ex1) (SGP.PEnd 0).
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
Definition ps0 : SR.post_spec := SR.PS 1172152 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 846716 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 846716 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcAl.

End BndP_Na_143.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001.
Module BndP_Na_144.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require asan.XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_144 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_by_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_404c852ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB2BRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F7xstep_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_aicB3kn0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS05xstepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F:xstep_f_eqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144>LibSegNa_aicC23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1a3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144@LibSegNa_aicCl1b3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl23kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl32BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl33NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl32BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl32F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl33PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl34planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl35regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl33kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl42BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl43NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl42BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl42F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl43PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl44planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl45regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCl43kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs12BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs13NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs12BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs12F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs13PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs14planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs15regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs13kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs22BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs23NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs22BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs22F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs23PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs24planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs25regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144?LibSegNa_aicCs23kn0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_4022922ITC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcB3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcC3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcD3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_144=LibSegNa_qpcE3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_aicB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [1172152].
Definition STOPS1 : list Z := [1172152] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-70$3$4$5$6$7+$21#78$21$:$;$<$=$>$?$10$11#8+$21-40#154:48+$21#10+$21#78+&6+$21#78#3#7???8000#154:30#7???8000#1549?0+&6$21#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",11'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18###80022938#20#&6+$21#10;#3#7???8000#1"%pstring).
Definition ss0 : sym_state := SS 720224 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-192), ELit 80); ((EVar 33), (0), ELit 8); ((EVar 33), (16), ELit 8); ((EVar 33), (120), ELit 8); ((EVar 33), (256), ELit 12)].
Definition F0L : list SR.region := [((EVar 2), (-192), 80); ((EVar 33), (0), 8); ((EVar 33), (16), 8); ((EVar 33), (120), 8); ((EVar 33), (256), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>2;8#11>2;8#5=#11>2;8,20##<1664+$2-<0$3$4$5$6$7+$21#10+$21#18+$21#18+$21-40#15?:78$=$>$?$10$11#8#8+$21-40+$21#10+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?,,23!$21#10,8#154898!$2-<0,8#154:30!$2-;8,8+&6+$21#78#3#7???8000!$2-;0,8+$21#78!$2-:8,8+$21#10!$2-:0,8#154:48!$2-98,8+$21-40!$2-90,8#8!$2-88,8$21!$2-80,8+$21#78!$2-78,8#:?=>0!$21#78,8#154:30!$21#,8#154:08!$21#10;,1^#?#???????????????!$21#10:,1^#?#???????????????!$21#109,1^#?#???????????????!$21#108,1^#?#???????????????!$21#100,8#'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18###80022938#20#&6+$21#10;#3#7???8000#1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1172152 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 720224 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 720224 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicB.

Module LibSegNa_aicC1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11#8#8+$21-40+$21#10+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18"%pstring).
Definition ss0 : sym_state := SS 792164 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7?058#7?058#5=#7?058,20##<1674+$2-<0$3$4$5$6$7+$21#10+$21#18+$21#20##30$=$>$?$10$11#8#8+$21-40+$21#10+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?,,?'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792164 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792164 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicC1.

Module LibSegNa_aicC2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11#8#8+$21-40+$21#10+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",?'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18"%pstring).
Definition ss0 : sym_state := SS 792180 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (16), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (16), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7?058#7?058#5=#7?058,20##<16:4+$2-<0$3$4$5$6$7+$21#10+$21#18+$21#50##20$=$>$?$10$11+$21#50#8+$21-40+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?,,10!$21#10,8#154918'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792180 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792180 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicC2.

Module LibSegNa_aicCl1a.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11+$21#50#8+$21-40+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$21-40,1$26'$26##??'&9$26#1#1#1!$21-38,8$28!$21-30,8$24!$21#50,1#'$28#17#2<"%pstring).
Definition ss0 : sym_state := SS 792228 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 48); ((EVar 33), (112), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-240), 48); ((EVar 33), (112), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##?4;5<+$2-?0$3$4$5$6$7$28+$21#50#30#2<#1>##1$?$10$11+$21#50$24#2?+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?,,1=!$2-?0,8+$21-40!$2->8,8#8!$2->0,8+$21#50!$2-=8,8+$21#18!$2-=0,8+$21#10!$2-<8,8#<16<4!$21#70,4#8'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$21-40,1$26'$26##??'&9$26#1#1#1!$21-38,8$28!$21-30,8$24!$21#50,1#'$28#17#2<,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792228 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792228 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCl1a.

Module LibSegNa_aicCl1b.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11+$21#50#8+$21-40+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",17'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$21-40,1$26'$26##??'&9$26#1#1#1!$21-38,8$28!$21-30,8$24!$21#50,1#'$28#2=#3??????'&8$28#7#2?#4000007"%pstring).
Definition ss0 : sym_state := SS 792228 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-240), ELit 48); ((EVar 33), (112), ELit 4)].
Definition F0L : list SR.region := [((EVar 2), (-240), 48); ((EVar 33), (112), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##?4;5<+$2-?0$3$4$5$6$7$28+$21#50+@#8&6$28#3#8#2<#1>##1$?$10$11+$21#50$24+@#8&6$28#3#7+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?,,1>!$2-?0,8+$21-40!$2->8,8#8!$2->0,8+$21#50!$2-=8,8+$21#18!$2-=0,8+$21#10!$2-<8,8#<16<4!$21#70,4#8'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$21-40,1$26'$26##??'&9$26#1#1#1!$21-38,8$28!$21-30,8$24!$21#50,1#'$28#2=#3??????'&8$28#7#2?#4000007,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792228 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792228 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCl1b.

Module LibSegNa_aicCl2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [519096].
Definition STOPS1 : list Z := [519096] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-?0$3$4$5$6$7$28$9$29$;$<$=$>$?$10$11$12$24$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 1002332 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7>;;8#7>;;8#5=#7>;;8,20##?4;6<+$2-?0$3$4$5$6$7$28$9$29$24$28$=$>$?$10$11$29$24$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 519096 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1002332 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 1002332 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCl2.

Module LibSegNa_aicCl3.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [792260].
Definition STOPS1 : list Z := [792260] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-?0$3$4$5$6$7$28+$21#50$:$;$<$=$>$?$10$11$29$13$2:$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",18'$2#7???7?802000#800000000000&$2#10($2-1000#1000'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$2-<8,8#<16<4!$2-=0,8+$21#10!$2-=8,8+$21#18!$2->0,8+$21#50!$2->8,8#8!$2-?0,8+$21-40'$29#1000#800000000000'$28#17#3??????'$2:#2?#4000007(+$29$28##1)$2-1000#1000+$29$28##1)$21##110+$29$28##1"%pstring).
Definition ss0 : sym_state := SS 1002348 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (80), ELit 24); ((EAlu Instr.ALU_ADD (EVar 41) (EVar 40)), (0), ELit 1)].
Definition F0L : list SR.region := [((EVar 33), (80), 24); ((EAlu Instr.ALU_ADD (EVar 41) (EVar 40)), (0), 1)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<16<4#<16<4#5=#<16<4,20##<16<4+$2-<0$3$4$5$6$7+$21#10+$21#18+$21#50$;$<$=$>$?$10$11+$21#50#8+$21-40$15$16$17$18$19$1:$1;$1<$1=$1>$1?,,1;!+$28$29#,1#!$21#60,8$29!$21#58,8$28!$21#50,8+$2:#2'$2#7???7?802000#800000000000&$2#10($2-1000#1000'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$2-<8,8#<16<4!$2-=0,8+$21#10!$2-=8,8+$21#18!$2->0,8+$21#50!$2->8,8#8!$2-?0,8+$21-40'$29#1000#800000000000'$28#17#3??????'$2:#2?#4000007(+$29$28##1)$2-1000#1000+$29$28##1)$21##110+$29$28##1,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 792260 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1002348 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 1002348 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCl3.

Module LibSegNa_aicCl4.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [720408].
Definition STOPS1 : list Z := [720408] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$2-78,8#:?=>0!$2-80,8+$21#78!$2-88,8$21!$2-90,8#8!$2-98,8+$21-40!$2-:0,8#154:48!$2-:8,8+$21#10!$2-;0,8+$21#78!$2-;8,8+&6+$21#78#3#7???8000!$2-<0,8#154:30!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-50,8$34!$2-58,8$35!$2-60,8$36!$2-68,8$37!$21#50,1$26'$26##??'&9$26#1#1#1!$21#58,8$28!$21#60,8$29!$21#70,4#8'$29#1000#800000000000'$28#17#3??????"%pstring).
Definition ss0 : sym_state := SS 792260 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-272), ELit 80); ((EVar 33), (32), ELit 24); ((EVar 33), (104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-272), 80); ((EVar 33), (32), 24); ((EVar 33), (104), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?>18#:?>18#5=#:?>18,20#$2;$2$3$4$5$6$7$2<$2=+$21#68+$21#30+&6+$21#68#3#7???8000#1#+$28$29#$11$2>$2?$30$31$32$33$34$35$36$37$1<$1=$1>$1?,,3;!$21#30,8+$28$29!$21#28,8$29!$21#20,8$29!$21#68,8+$28$29!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8$12!$2-=8,8$9!$2-=0,8+$21#10!$2-<8,8#<16<<'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$2-78,8#:?=>0!$2-80,8+$21#78!$2-88,8$21!$2-90,8#8!$2-98,8+$21-40!$2-:0,8#154:48!$2-:8,8+$21#10!$2-;0,8+$21#78!$2-;8,8+&6+$21#78#3#7???8000!$2-<0,8#154:30!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-50,8$34!$2-58,8$35!$2-60,8$36!$2-68,8$37!$21#50,1$26'$26##??'&9$26#1#1#1!$21#58,8$28!$21#60,8$29!$21#70,4#8'$29#1000#800000000000'$28#17#3??????,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720408 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792260 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792260 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCl4.

Module LibSegNa_aicCs1.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [792260].
Definition STOPS1 : list Z := [792260] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10+$21#18$:$;$<$=$>$?$10$11+$21#50#8+$21-40+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",16'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$21-40,1$26'$26##??'&9$26#1##!$21-40,8$23!$21-38,8$24!$21-30,8$25!$21#50,1#"%pstring).
Definition ss0 : sym_state := SS 792228 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (80), ELit 36)].
Definition F0L : list SR.region := [((EVar 33), (80), 36)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<16<4#<16<4#5=#<16<4,20##<16<4+$2-<0$3$4$5$6$7+$21#10+$21#18+$21#50$23$24##$?$10$11+$21#50#8+$21-40+$21#70+&6+$21#10#3#7???8000#154898#7???8000#7???8000#154:08+&6$21#3#7???8000$1<$1=$1>$1?,,19!$21#50,8$23!$21#58,8$24!$21#60,8$25!$21#70,4#8'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$21-40,1$26'$26##??'&9$26#1##!$21-40,8$23!$21-38,8$24!$21-30,8$25,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 792260 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792228 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792228 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCs1.

Module LibSegNa_aicCs2.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_404c85.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_404c85.IT.
Definition ENDS : list Z := [720408].
Definition STOPS1 : list Z := [720408] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#10$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2:'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$2-78,8#:?=>0!$2-80,8+$21#78!$2-88,8$21!$2-90,8#8!$2-98,8+$21-40!$2-:0,8#154:48!$2-:8,8+$21#10!$2-;0,8+$21#78!$2-;8,8+&6+$21#78#3#7???8000!$2-<0,8#154:30!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-50,8$34!$2-58,8$35!$2-60,8$36!$2-68,8$37!$21#50,1$26'$26##2<'&9$26#1##!$21#70,4#8"%pstring).
Definition ss0 : sym_state := SS 792260 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-272), ELit 80); ((EVar 33), (32), ELit 24); ((EVar 33), (104), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-272), 80); ((EVar 33), (32), 24); ((EVar 33), (104), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#:?>18#:?>18#5=#:?>18,20#$2;$2$3$4$5$6$7$2<$2=+$21#68+$21#30+&6+$21#68#3#7???8000##++$21&6$26#1#51#$11$2>$2?$30$31$32$33$34$35$36$37$1<$1=$1>$1?,,37!$21#30,8++$21&6$26#1#51!$21#28,8+$21#51!$21#20,8+$21#51!$21#68,8++$21&6$26#1#51!$2-108,8$17!$2-100,8$16!$2-?8,8$15!$2-?0,8$14!$2->8,8$13!$2->0,8$12!$2-=8,8$9!$2-=0,8+$21#10!$2-<8,8#<16<<'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'$21#6;6040#7????????>>8&$21#8)##7???7000#100000001000$21##110#&6$21#3#7???8000#22($21##110)$2-1000#1000$21##110)##10000#6:6000$21##110)$2-1000#1000$21-40#18)##10000#6:6000$21-40#18!$2-78,8#:?=>0!$2-80,8+$21#78!$2-88,8$21!$2-90,8#8!$2-98,8+$21-40!$2-:0,8#154:48!$2-:8,8+$21#10!$2-;0,8+$21#78!$2-;8,8+&6+$21#78#3#7???8000!$2-<0,8#154:30!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-48,8$33!$2-50,8$34!$2-58,8$35!$2-60,8$36!$2-68,8$37!$21#50,1$26'$26##2<'&9$26#1##!$21#70,4#8,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 720408 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_404c85.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 792260 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_404c85.IT BndT_Na_001.SegItab_Na_404c85.IT_sound BF NX0 BR XSTEP F0 PSS plan 792260 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_aicCs2.

Module LibSegNa_qpcB.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [1172152].
Definition STOPS1 : list Z := [1172152] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#20+$21#30$:$;$<$=$>$?$10$11+$21#70#7???8000+&6+$21#20#3#7???8000+&6+$21#70#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2<'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$2-88,8#<?028!$2-90,8+$21#20!$2-98,8+$21#18!$2-:0,8+$21-1?0!$2-:8,8#7???8000!$2-;0,8$30!$2-;8,8#7???8000"%pstring).
Definition ss0 : sym_state := SS 849248 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (32), ELit 8); ((EVar 33), (48), ELit 8); ((EVar 33), (112), ELit 8); ((EVar 33), (248), ELit 12)].
Definition F0L : list SR.region := [((EVar 33), (32), 8); ((EVar 33), (48), 8); ((EVar 33), (112), 8); ((EVar 33), (248), 12)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#11>2;8#11>2;8#5=#11>2;8,20##<?5>4+$2-<0$3$4$5$6$7+$21#20+$21#30+$21#38#$<$=$>$?$10$11+$21#70+&6+$21#30#3#7???8000+&6+$21#20#3#7???8000+&6+$21#70#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,31!$21#30,8#154898!$21#70,8#151088!$21#20,8#151060!$21#100,4^#?#???????????????!$21#?8,8#'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$2-88,8#<?028!$2-90,8+$21#20!$2-98,8+$21#18!$2-:0,8+$21-1?0!$2-:8,8#7???8000!$2-;0,8$30!$2-;8,8#7???8000,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1172152 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 849248 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 849248 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcB.

Module LibSegNa_qpcC.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#20+$21#30$:$;$<$=$>$?$10$11+$21#70+&6+$21#30#3#7???8000+&6+$21#20#3#7???8000+&6+$21#70#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2<'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$2-88,8#<?028!$2-90,8+$21#20!$2-98,8+$21#18!$2-:0,8+$21-1?0!$2-:8,8#7???8000!$2-;0,8$30!$2-;8,8#7???8000"%pstring).
Definition ss0 : sym_state := SS 849380 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7?058#7?058#5=#7?058,20##<?5?4+$2-<0$3$4$5$6$7+$21#20+$21#30+$21#40##30$=$>$?$10$11+$21#70+&6+$21#30#3#7???8000+&6+$21#20#3#7???8000+&6+$21#70#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2<'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$2-88,8#<?028!$2-90,8+$21#20!$2-98,8+$21#18!$2-:0,8+$21-1?0!$2-:8,8#7???8000!$2-;0,8$30!$2-;8,8#7???8000,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 849380 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 849380 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcC.

Module LibSegNa_qpcD.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-<0$3$4$5$6$7+$21#20+$21#30$:$;$<$=$>$?$10$11+$21#70+&6+$21#30#3#7???8000+&6+$21#20#3#7???8000+&6+$21#70#3#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",2>'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$2-88,8#<?028!$2-90,8+$21#20!$2-98,8+$21#18!$2-:0,8+$21-1?0!$2-:8,8#7???8000!$2-;0,8$30!$2-;8,8#7???8000!$21-1?0,8#154:08!$21-150,8+$21-1>0"%pstring).
Definition ss0 : sym_state := SS 849396 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (48), ELit 8); ((EVar 33), (264), ELit 16)].
Definition F0L : list SR.region := [((EVar 33), (48), 8); ((EVar 33), (264), 16)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7?058#7?058#5=#7?058,20##<?0;4+$2-80$3$4$5$6$7+$21#20+$21#18+$21#118##10$=$>$?$10$11+$21#128#7???8000$30#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,31!$21#110,8+$21-1>0!$21#108,8+$21-1?0!$21#30,8#151370'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$2-88,8#<?028!$2-90,8+$21#20!$2-98,8+$21#18!$2-:0,8+$21-1?0!$2-:8,8#7???8000!$2-;0,8$30!$2-;8,8#7???8000!$21-1?0,8#154:08!$21-150,8+$21-1>0,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 849396 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 849396 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcD.

Module LibSegNa_qpcE.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#20+$21#18$:$;$<$=$>$?$10$11+$21#128#7???8000$14#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",25'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?"%pstring).
Definition ss0 : sym_state := SS 848052 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (296), ELit 8)].
Definition F0L : list SR.region := [((EVar 33), (296), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7?058#7?058#5=#7?058,20##<?0>0+$2-80$3$4$5$6$7+$21#20+$21#18+$21#130##10$=$>$?$10$11+$21#130#7???8000$14#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,26!$21#128,8#4000'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 848052 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 848052 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcE.

End BndP_Na_144.
Module BndP_Na_145.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegCodec.  Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require asan.XIcptA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegPlanAuto OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.SegPlanJoin OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0147.Na0PlanKitIt OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.XIcptA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.XIcptAs0Kit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0128. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Mh_0178.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.seg Require BndT_Na_001.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_BndP_Na_145 () := "C47Corelib5Lists7ListDef3mapK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_ok_fastC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0128;SegPlanFast3SGF<cert_by_fastC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C69OSSVerify5KrLib3seg;BndT_Na_001ASegItab_Na_4022922ITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_CPYC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_SETC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5X_LENC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_LOC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit5RO_HIC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF2BFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0147:Na0PlanKit2A0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF2BRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F7xstep_fC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7SegPlan3SGP;xstep2_noneC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcF3kn0C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178;XIcptAs0Kit5XIAS05xstepC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib4asan7Mh_0178:XIcptAFast6XIAS0F:xstep_f_eqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcG3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcH3kn0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ2BFC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ3NX0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ2BRC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ2F0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ3PSSC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ4planC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ5regs0C1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib3seg7Mh_0224;BndP_Na_145=LibSegNa_qpcZ3kn0C1?~~~~~~~~~~~~~~~".

Module LibSegNa_qpcF.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [1374112].
Definition STOPS1 : list Z := [1374112] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#20+$21#18$:$;$<$=$>$?$10$11+$21#130#7???8000$14#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [].
Definition ss0 : sym_state := SS 848096 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#14?7:0#14?7:0#5=#14?7:0,20##<?0>8+$2-80$3$4$5$6$7+$21#20+$21#18#4000$;$<$=$>$?$10$11+$21#130#7???8000$14#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 1374112 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 848096 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 848096 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcF.

Module LibSegNa_qpcG.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [520280].
Definition STOPS1 : list Z := [520280] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-80$3$4$5$6$7+$21#20+$21#18$23$;$<$=$>$?$10$11+$21#130#7???8000$14#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",27'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$22#,8#150=08!$22#10,4#400"%pstring).
Definition ss0 : sym_state := SS 848104 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 33), (288), ELit 8); ((EVar 33), (304), ELit 8); ((EVar 33), (320), ELit 4)].
Definition F0L : list SR.region := [((EVar 33), (288), 8); ((EVar 33), (304), 8); ((EVar 33), (320), 4)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#7?058#7?058#5=#7?058,20##<><=4+$2-50$3$4$5$6$7$21+$21#18+$21#148##48$=$>$?$10$11+$21#148$2?+$21#178#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,2:!$21#140,4#400!$21#130,8$23!$21#120,8$23'$2#7???7?802000#800000000000&$2#10($2-1000#1000%#150000#158000!##15?:78,8#7???8000!##15?:80,4#1'+$21-1?0#6;6000#7????????<78&+$21-1?0#8)##7???7000#100000001000+$21-1?0##380)$2-1000#1000+$21-1?0##380)##10000#6:6000+$21-1?0##380#&6+$21-1?0#3#7???8000#22&$21#8($21##190#&6$21#3#7???8000#32'$22#6;6000#7?????????>0&$22#8)##7???7000#100000001000$22##18#&6$22#3#7???8000#3)$2-1000#1000$22##18)##10000#6:6000$22##18)$21##190$22##18###8002219:#40###80022938#20!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32!$2-58,8#<><5<!$2-60,8$21!$2-68,8+$21#18!$2-70,8$22!$2-78,8$2?!$22#,8#150=08!$22#10,4#400,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 848104 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 848104 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcG.

Module LibSegNa_qpcH.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [848248].
Definition STOPS1 : list Z := [848248] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$21+$21#18$:$;$<$=$>$?$10$11+$21#148$13+$21#178#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := [KRange (EVar 2) 140735332491264 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-4096)) (ELit 4096)].
Definition ss0 : sym_state := SS 847060 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [((EVar 2), (-76), ELit 8)].
Definition F0L : list SR.region := [((EVar 2), (-76), 8)].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<?178#<?178#5=#<?178,20##<><><+$2-50$3$4$5$6$7$21+$21#18+$21#178+$2-48+$2-4<$=$>$?$10$11+$21#148$13+$21#178#7???8000$16$17$18$19$1:$1;$1<$1=$1>$1?,,5!$2-4<,4#!$2-48,4#'$2#7???7?802000#800000000000&$2#10($2-1000#1000,3<!"%pstring).
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

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 847060 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 847060 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcH.

Module LibSegNa_qpcZ.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := BndT_Na_001.SegItab_Na_402292.ITR.
Definition IT : itab := BndT_Na_001.SegItab_Na_402292.IT.
Definition ENDS : list Z := [847120].
Definition STOPS1 : list Z := [847120] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_E) ",20#$1+$2-50$3$4$5$6$7$8$9$:$;$<$=$>$?$10$11$12$13$14$15$16$17$18$19$1:$1;$1<$1=$1>$1?"%pstring).
Definition kn0 : list kentry := Eval vm_compute in (SegCodec.run (SegCodec.lst SegCodec.sc_kentry) ",;'$2#7???7?802000#800000000000&$2#10($2-1000#1000!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32"%pstring).
Definition ss0 : sym_state := SS 847084 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := 1000.

Definition BR : list SGP.bfact := [].

Definition XSTEP := XIAS0.xstep.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

Definition ex1 : list SGA.aitem * (Z * sym_state) := Eval vm_compute in (SegCodec.run (SegCodec.sc_pair (SegCodec.lst SegCodec.sc_aitem) (SegCodec.sc_pair SegCodec.sc_Z SegCodec.sc_sstate)) ",1!!,2#<>=10#<>=10#5=#<>=10,20#$2;$2$3$4$5$6$7$2<$2=$:$;$<$=$>$?$10$11$2>$2?$30$31$32$17$18$19$1:$1;$1<$1=$1>$1?,,;'$2#7???7?802000#800000000000&$2#10($2-1000#1000!$2-8,8$2;!$2-10,8$2<!$2-18,8$2=!$2-20,8$2>!$2-28,8$2?!$2-30,8$30!$2-38,8$31!$2-40,8$32,3<!"%pstring).
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
Definition ps0 : SR.post_spec := SR.PS 847120 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS BndT_Na_001.SegItab_Na_402292.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 847084 regs0 kn0 = true.
Proof. apply (Mh_0128.SegPlanFast.SGF.cert_by_fast _ _ Mh_0178.XIcptAFast.XIAS0F.xstep_f_eq). vm_cast_no_check (@eq_refl bool true). Qed.

Section XH.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Definition seg_sound_ax := as0_plan_sound_it BndT_Na_001.SegItab_Na_402292.IT BndT_Na_001.SegItab_Na_402292.IT_sound BF NX0 BR XSTEP F0 PSS plan 847084 regs0 kn0 cert (XIAS0.xstep_ok HFILL HCOPY HTLS NX0 BR F0).
End XH.
End LibSegNa_qpcZ.

End BndP_Na_145.
