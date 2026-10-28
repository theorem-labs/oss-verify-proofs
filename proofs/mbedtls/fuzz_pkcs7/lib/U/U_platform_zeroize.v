(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_platform_zeroize () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "platform_zeroize_post"].


Definition U_PLATFORM_ZEROIZE : Z := 0x259d4.
Definition U_MEMSET_FUNC : Z := 0x48370.      (* [comment removed for export] *)

(* [comment removed for export] *)
Notation PLATFORM_ZEROIZE_STACK := 16 (only parsing).

Definition platform_zeroize_post (segs : list Segment) (L : heap_layout)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_platform_zeroize ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O16.O15.O14.O13.R10.R?.R>.O12.O11.R=.R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(8.O16.)O5.(9.(2.&40.))R1.(:.O18.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.O4.(10.O4.O3.))(<.(=.$>.$>.)(?.$>.$>.(11.(12.&40.O15.)+10.)(12.&40.O15.))(13.(=.$>.$>.))))O1.R1.)(4.(14.O18.O1.R1.)(4.(15.O18.R1.)(4.(16.O18.R1.O4.(<.$17.(18.(19.O3.)(1:.(2.&8.)(1;.&8.=)(19.O3.)))(13.$17.)))(4.(1<.O18.R1.O2.(12.&40.O15.))(1=.O18.O17.R1.)))))))))))))))))))))))")
(* [comment removed for export] *).

Definition platform_zeroize_stmt (segs : list Segment) (L : heap_layout) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_platform_zeroize ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$>.Pn,$>.Plo,$>.Pjunk,(1?.(2.&8.))P,(16.O4.R5.R4.(<.$17.(18.(19.R3.)R1.)(13.$17.)))P,(20.=R4.)P,(21.=R6.)P,(1<.O4.R8.R5.(12.&40.R28.))P,(20.R6.(11.(12.&40.R29.)+10.))P,(20.(22.O3.)R7.)P,(5.$>.(23.(12.&40.R2;.)+10.)=)P,(24.(20.(10.R;.R:.)R9.)(20.(12.&40.R2<.)R;.))P,(1=.O4.O3.R=.)P,(25.O3.O1.+8.)P,(20.(26.O3.)(22.O3.))P,(24.(20.(10.R?.R>.)(27.O3.))(20.(26.O3.)R?.))P,(15.O4.R11.)P,(5.(2.&40.)R2:.(1;.&40.R11.))P,(5.(2.&40.)R2:.(1;.&40.R11.))(28.O4.(29.O4.O3.R35.R34.R33.R32.R2>.R2=.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R16.R15.R13.R12.R11.R14.)(6.(7.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(1;.&40.O2.)R15.(9.(2.&40.))R14.(:.O4.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
