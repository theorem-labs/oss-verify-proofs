(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape MState Mem Cells Step Frame HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepCrt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow AUnw ARt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_alloc_lib.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_alloc_lib A_crt_stmts.
Import ListNotations.
Open Scope Z_scope.

Ltac drop_last H :=
  lazymatch type of H with
  | _ /\ (_ /\ _) => let a := fresh in let b := fresh in destruct H as [a b]; split; [exact a| drop_last b]
  | _ /\ _ => exact (proj1 H)
  end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_crt_free_stmt2 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.LibA.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "OSSVerify.KrLib.LibA.ARt.presA"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Spec.RepCrt.CRT_SIZE"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.LibA.ARt.havol"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Spec.RepCrt.crt_blocks"; "OSSVerify.KrLib.LibA.ARt.hfr"; "OSSVerify.KrLib.LibA.ARt.HM"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.fst"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.Spec.RepCrt.crt_zero"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.RepCrt.co_rawp"; "OSSVerify.KrLib.Spec.RepCrt.co_ob"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Spec.RepCrt.crt_own"; "OSSVerify.KrLib.Spec.RepCrt.crt_junk"; "OSSVerify.KrLib.Spec.RepCrt.crt_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.Lists.List.NoDup"; "OSSVerify.KrLib.Spec.RepCrt.co_rawlen"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.Lib.HeapIface.client_wrange"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.LibA.ARt.fdata"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.LibA.ARt.arl_tp"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "Stmts.x509_crt_free_postA2"].


Section Stmts.
  Variable segs : list Segment.
  Variable R : art_layout.
  Variable HIA : artA segs R.
  Variable PK : pk_class segs.
  Let AL := arl_AL R.
  Variables (PHIcf : Z -> Z) (FFRcf : Z -> Z -> Z) (STKcf : Z).

  Definition x509_crt_free_postA2
      (h : HST segs R HIA) (LBo LB LF : list blk)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (A : Z) (f : crt_own) (lo d : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_crt_free_stmt2 ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VR,VHIA,)Lh',(5.Vsegs,VR,VHIA,)(1.(6.$7.)LLBo',(6.$7.)(8.(9.$0.R14.(:.(;.(<.O18.O17.O16.O15.R13.R12.R11.O14.O13.R10.R?.R>.R=.R<.R;.R:.R9.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(=.O18.)O7.(>.(2.&40.))R4.(?.Vsegs,))R3.))(8.(10.Vsegs,R4.)(8.(11.Vsegs,R4.O4.(12.&40.O17.))(8.(13.O1.R3.)(8.(14.Vsegs,VR,(15.$7.R1.O1:.)O19.(12.&40.O17.)(16.VR,)(17.Vsegs,VR,VHIA,O1<.)(18.(19.$1:.$1:.)(1;.$1:.$1:.O6.(1<.O6.$1=.))(1>.(19.$1:.$1:.)))O2.R4.)(8.(9.$1:.(1?.Vsegs,VR,VHIA,R2.)(1?.Vsegs,VR,VHIA,O1<.))(8.(9.$1:.(17.Vsegs,VR,VHIA,R2.)(17.Vsegs,VR,VHIA,O1<.))(8.(9.$1:.(20.Vsegs,VR,VHIA,R2.)(20.Vsegs,VR,VHIA,O1<.))(8.(21.Vsegs,VR,VHIA,R2.R3.)(8.Px,$1:.P,(22.Vsegs,VR,VHIA,O1<.R1.)(22.Vsegs,VR,VHIA,R4.R2.)(8.(23.(24.Vsegs,VR,VHIA,R2.)(1<.(24.Vsegs,VR,VHIA,O1<.)A1.VPHIcf,(25.(26.$7.(27.O5.)))))(8.(23.(28.Vsegs,VR,VHIA,R2.)(1<.(28.Vsegs,VR,VHIA,O1<.)A2.VFFRcf,(25.(26.$7.(27.O5.)))O3.))(8.(29.Vsegs,VR,VHIA,R2.(15.$7.R1.O1:.)O19.R4.)(8.Pb,$7.P,(2:.$7.R1.R2.)(2:.$7.R2.O1;.)(8.Pb,$7.P,(2:.$7.R1.O1;.)P,(2;.(2:.$1:.(2<.$1:.$1:.R2.)(2=.(19.$1:.$1:.)$1:.(2<.$1:.$1:.)(27.O5.))))(2:.$7.R3.R4.)(8.(2>.Vsegs,R4.O6.)P,(2?.(9.$1:.(30.O5.)=)(9.(2.&40.)(31.O5.)(32.&40.+1.)))Pb,$7.P,(2:.$7.R1.R3.)(2;.(2:.$1:.(2<.$1:.$1:.R2.)(2=.(19.$1:.$1:.)$1:.(2<.$1:.$1:.)(27.O5.)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition x509_crt_free_stmtA2 (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_crt_free_stmt2 ()) "Ph,(5.Vsegs,VR,VHIA,)PLBo,(6.$7.)PLB,(6.$7.)PLF,(6.$7.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(33.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.PA,$1:.Pf,$34.Pj,$35.Plo,$1:.Pd,$1:.P,(29.Vsegs,VR,VHIA,R2<.(15.$7.R2;.R2:.)R29.R7.)P,(21.Vsegs,VR,VHIA,R2=.R7.)P,(36.Vsegs,VPK,R9.(15.$7.R2=.R2<.)R7.R6.R5.)P,Pb,$7.P,(2:.$7.R1.(27.R8.))(2:.$7.R2.R30.)P,(37.=R9.)P,(9.$1:.(38.R:.+8.)=)P,(39.$1:.(2=.(19.$1:.$1:.)$1:.(2<.$1:.$1:.)(15.$7.R31.R30.)))P,(37.(3:.R;.)(3;.+2.+28.))P,(3<.Vsegs,VAL,(22.Vsegs,VR,VHIA,R34.)R?.R=.$1=.)P,(3=.(3>.VR,)(15.$7.R33.(3?.R32.))R;.(1?.Vsegs,VR,VHIA,R35.)R>.$1=.)P,(2?.(23.(1<.R?.$1=.)R<.)(23.(12.&40.R31.)R?.))P,(11.Vsegs,R12.R=.(12.&40.R32.))P,(23.(16.VR,)R>.)P,(23.R?.(40.(12.&40.R34.)VSTKcf,))P,(23.(12.&40.R35.)(1?.Vsegs,VR,VHIA,R3:.))P,(9.$1:.(38.(12.&40.R36.)+10.)=)P,(10.Vsegs,R17.)P,(9.(2.&40.)R36.(32.&40.(41.VR,)))P,(23.(1<.(24.Vsegs,VR,VHIA,R3>.)A1.VPHIcf,(25.(26.$7.(27.R16.))))$42.)P,(43.VR,R18.$1=.R14.)P,(23.(1<.(28.Vsegs,VR,VHIA,R40.)A2.VFFRcf,(25.(26.$7.(27.R18.)))R15.)$44.)P,(9.(2.&40.)R34.(32.&40.R1:.))(45.Vsegs,(46.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1;.R1:.R18.R17.R1=.R1<.)(:.(;.(<.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(32.&40.O1.)R1>.(>.(2.&40.))R1=.(?.Vsegs,))R1<.))")
(* [comment removed for export] *).

  End Stmts.
