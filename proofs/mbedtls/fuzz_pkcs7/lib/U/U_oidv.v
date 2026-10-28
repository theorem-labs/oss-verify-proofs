(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_string U_oid.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_oidv () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.U.U_oid.MBEDTLS_ERR_OID_NOT_FOUND"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "oid_vres"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "oid_lookup1v_post"].


(* [comment removed for export] *)
Definition oid_vres (r : Z) (v v0 : word) (VALS : list Z) : Prop :=
  (r = MBEDTLS_ERR_OID_NOT_FOUND /\ v = v0) \/ (r = 0 /\ In (bv_unsigned v) VALS).

Lemma oid_vres_notfound : forall v0 VALS, oid_vres MBEDTLS_ERR_OID_NOT_FOUND v0 v0 VALS.
Proof. intros. left. split; reflexivity. Qed.
Lemma oid_vres_found : forall v v0 VALS, In (bv_unsigned v) VALS -> oid_vres 0 v v0 VALS.
Proof. intros. right. split; [reflexivity| assumption]. Qed.

Definition oid_lookup1v_post (segs : list Segment) (L : heap_layout)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (EXT STACK lo : Z) (v0 : word) (VALS : list Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_oidv ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.(2.&40.)Lv,(2.&40.)(5.(6.$0.R13.(7.(8.O18.O17.O16.O15.R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(9.O18.)O7.(:.(2.&40.))R3.(;.O1:.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O17.)O5.)(12.&40.O17.))(13.(>.$4.$4.))))O1.R3.)(5.(14.O1:.O1.R3.)(5.(15.O1:.R3.)(5.(6.(2.&40.)R?.(16.&40.R2.))(5.(17.(6.$4.R2.=)(6.$4.R2.$18.))(5.(19.O1:.R3.O6.(=.$1:.(1;.R1.)(13.$1:.)))(5.(1<.R2.R1.O3.O2.)(5.(1=.O1:.R3.O4.(12.&40.O17.))(1>.O1:.O19.R3.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition oid_lookup1v_stmt (segs : list Segment) (L : heap_layout) (ENTRY TBL TBLN STACK : Z) (VALS : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_oidv ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))POID,$4.PEXT,$4.PP,$4.PLEN,$4.Plo,$4.Ptg,(2.&40.)Ppd,(2.&40.)Pv0,(2.&40.)Pxs,(20.(2.&8.))P,(19.O7.R:.R9.(21.R4.R3.R6.R7.))P,(22.O7.R;.R8.R2.)P,(6.$4.(23.(24.(2.&8.)R3.))R8.)P,(19.O7.R=.R;.(=.$1:.(1;.R5.)(13.$1:.)))P,(17.(25.(10.R<.+4.)R=.)(25.(10.R=.+18.)R<.))P,(17.(25.(10.R=.+4.)R<.)(25.(10.R<.R;.)R=.))P,(6.$4.(26.R?.+8.)=)P,(6.$4.(26.R?.+4.)=)P,(27.=R11.)P,(27.=R11.)P,(27.=R11.)P,(1=.O7.R15.R10.(12.&40.R35.))P,(25.R11.(11.(12.&40.R36.)O2.))P,(25.(28.O6.)R12.)P,(6.$4.(26.(12.&40.R38.)+10.)=)P,(17.(25.(10.R18.+18.)R14.)(25.(12.&40.R39.)R18.))P,(17.(25.(10.R18.+4.)R15.)(25.(12.&40.R3:.)R18.))P,(17.(25.(10.R18.R17.)R16.)(25.(12.&40.R3;.)R18.))P,(15.O7.R1<.)P,(1>.O7.O6.R1=.)P,(29.O6.O4.O3.)P,(25.(2:.O6.)(28.O6.))P,(17.(25.(10.R1>.+4.)(2;.O6.))(25.(2:.O6.)R1>.))P,(6.(2.&40.)R39.(16.&40.R20.))P,(6.(2.&40.)R39.(16.&40.R20.))(2<.O7.(2=.O7.O6.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R21.O2.R1>.R1;.O1.R23.)(7.(8.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(16.&40.O5.)R24.(:.(2.&40.))R23.(;.O7.)))")
(* [comment removed for export] *).

