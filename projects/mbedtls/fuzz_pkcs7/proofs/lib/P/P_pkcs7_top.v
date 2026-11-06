(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep AEvt HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import SInv.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pkcs7_top () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Spec.SInv.si_P"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "PKCS7_SIZE"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Spec.SInv.si_fp"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "pkcs7_zero"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.sub"; "PKCS7_PARSE_STACK"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "Stmts.pkcs7_parse_der_post"; "PKCS7_FREE_STACK"; "Stmts.pkcs7_free_post"].


Definition PKCS7_SIZE : Z := 1440.
Definition pkcs7_zero (segs : list Segment) (m : mem) (A : Z) : Prop :=
  rw_cells segs m A [CB 1440 (repeat (Z_to_bv 8 0) 1440)].

(* [comment removed for export] *)
Definition PKCS7_PARSE_STACK : Z := 60000.
Definition PKCS7_FREE_STACK : Z := 20000.

Section Stmts.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Variable P7T : Type.
  (* [comment removed for export] *)
  Variable p7rep : P7T -> mem -> list blk -> list blk -> Z -> Prop.

  Definition pkcs7_parse_der_post (SI : sinv L)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : HST segs L HI) (LB : list blk) (A lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_top ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VL,VHI,)Lh',(5.Vsegs,VL,VHI,)(1.VP7T,Lst,VP7T,(1.(6.$7.)LLBn,(6.$7.)(8.(9.$0.R15.(:.(;.(<.O18.O17.O16.O15.R14.R13.R12.O14.O13.R11.R10.R?.R>.R=.R<.R;.R:.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R9.R8.R7.R6.)O8.(=.O18.)O7.(>.(2.&40.))R5.(?.Vsegs,))R4.))(8.(10.Vsegs,R5.)(8.(11.Vsegs,VL,R5.)(8.(12.VL,O19.R5.)(8.(13.Vsegs,R5.O3.(14.&40.O17.))(8.(15.O1.R4.)(8.(9.$16.(17.Vsegs,VL,VHI,R3.)(17.Vsegs,VL,VHI,O6.))(8.A5.Vp7rep,R2.R5.R1.O5.O4.(8.(18.Vsegs,VL,VHI,R3.(19.$7.R1.O5.)R5.R4.)(1:.Vsegs,VL,O5.(14.&40.O17.)(19.(1;.$16.$16.)(1<.(1;.$16.$16.)(1=.$16.$16.O4.(1>.O4.$1?.))(20.(1;.$16.$16.)))(21.VL,O19.))O2.R5.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition pkcs7_parse_der_stmt (SI : sinv L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_top ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.Vsegs,VL,VHI,)PLB,(6.$7.)PA,$16.PDATA,$16.Pn,$16.Plo,$16.Pbs,(6.(2.&8.))P,(18.Vsegs,VL,VHI,R7.R6.R9.R8.)P,(23.Vsegs,R:.R6.)P,(9.$16.(24.R7.+8.)=)P,(25.Vsegs,R<.R7.R4.)P,(9.$16.(26.(27.(2.&8.)R5.))R7.)P,(8.(28.=R8.)(29.R8.(2:.+2.+1:.)))P,(29.=R:.)P,(2;.VL,R=.(14.&40.R30.)R;.R:.)P,(2<.(28.(1>.R<.R;.)R:.)(28.(14.&40.R31.)R<.))P,(2<.(28.(1>.R>.$1?.)R=.)(28.(1>.R=.R<.)R>.))P,(28.(14.&40.R33.)R?.)P,(28.(1>.R10.$1?.)(17.Vsegs,VL,VHI,R12.))P,(13.Vsegs,R15.R>.(14.&40.R35.))P,(28.(2=.VL,)R?.)P,(28.R10.(2>.(14.&40.R37.)$2?.))P,(9.$16.(24.(14.&40.R38.)+10.)=)P,(28.(14.&40.R39.)(17.Vsegs,VL,VHI,R17.))P,(10.Vsegs,R1:.)P,(11.Vsegs,VL,R1;.)P,(12.VL,O2.R1<.)P,(9.(2.&40.)R3;.(30.&40.(31.VL,)))P,(9.(2.&40.)R36.(30.&40.R1:.))P,(9.(2.&40.)R36.(30.&40.R1:.))P,(9.(2.&40.)R36.(30.&40.R1:.))(32.Vsegs,R20.(33.O2.R42.R41.R40.R3?.R3;.R3:.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R23.R22.R1?.R1>.R1=.R1:.R21.R20.)(;.(<.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R23.(30.&40.O1.)R22.(>.(2.&40.))R21.(?.Vsegs,)))")
(* [comment removed for export] *).

  Definition pkcs7_free_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : HST segs L HI) (LB : list blk) (A lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_top ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VL,VHI,)Lh',(5.Vsegs,VL,VHI,)(1.(6.$7.)LLBx,(6.$7.)(8.(9.$0.R14.(:.(;.(<.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(=.O18.)O7.(>.(2.&40.))R4.(?.Vsegs,))R3.))(8.(10.Vsegs,R4.)(8.(11.Vsegs,VL,R4.)(8.(13.Vsegs,R4.O3.(14.&40.O17.))(8.(15.O1.R3.)(8.(9.$16.(17.Vsegs,VL,VHI,R2.)(17.Vsegs,VL,VHI,O6.))(8.(23.Vsegs,R4.O4.)(8.(18.Vsegs,VL,VHI,R2.(19.$7.R1.O5.)R4.R3.)(1:.Vsegs,VL,O5.(14.&40.O17.)(1<.(1;.$16.$16.)(1=.$16.$16.O4.(1>.O4.$1?.))(20.(1;.$16.$16.)))O2.R4.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition pkcs7_free_stmt (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_top ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.Vsegs,VL,VHI,)PLB,(6.$7.)PLBn,(6.$7.)PA,$16.Plo,$16.Pst,VP7T,P,(18.Vsegs,VL,VHI,R6.(19.$7.R4.R5.)R8.R7.)P,A5.Vp7rep,R2.R9.R5.R6.R4.P,(28.(14.&40.R2:.)R5.)P,(28.(1>.R6.$1?.)(17.Vsegs,VL,VHI,R9.))P,(13.Vsegs,R<.R6.(14.&40.R2<.))P,(28.(2=.VL,)R7.)P,(28.R8.(2>.(14.&40.R2>.)$34.))P,(9.$16.(24.(14.&40.R2?.)+10.)=)P,(28.(14.&40.R30.)(17.Vsegs,VL,VHI,R>.))P,(10.Vsegs,R11.)P,(11.Vsegs,VL,R12.)P,(9.(2.&40.)R31.(30.&40.(31.VL,)))P,(9.(2.&40.)R2<.(30.&40.R?.))(32.Vsegs,R14.(35.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R13.R12.R10.R?.R15.R14.)(;.(<.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(30.&40.O1.)R16.(>.(2.&40.))R15.(?.Vsegs,)))")
(* [comment removed for export] *).
End Stmts.
