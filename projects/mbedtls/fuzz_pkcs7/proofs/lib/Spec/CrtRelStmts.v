(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep AEvt HeapIface Asn1Aux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepCrt CrtStmts.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_CrtRelStmts () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.AStep.statics_ok"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "Corelib.Init.Datatypes.app"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.fst"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Spec.RepCrt.pk_rep"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Spec.CrtStmts.PK_FREE_STACK"; "OSSVerify.KrLib.Lib.HeapIface.hl_stack"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_tp"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "Stmts.pk_free_post2"; "OSSVerify.KrLib.Spec.RepCrt.crt_blocks"; "OSSVerify.KrLib.Spec.RepCrt.crt_zero"; "OSSVerify.KrLib.Spec.RepCrt.CRT_SIZE"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Spec.RepCrt.co_rawp"; "OSSVerify.KrLib.Spec.RepCrt.co_ob"; "OSSVerify.KrLib.Spec.RepCrt.crt_own"; "OSSVerify.KrLib.Spec.RepCrt.crt_junk"; "OSSVerify.KrLib.Spec.RepCrt.crt_at"; "OSSVerify.KrLib.Spec.CrtStmts.X509_CRT_FREE_STACK"; "Stmts.x509_crt_free_post2"].


Section Stmts.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Variable PK : pk_class segs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pk_free_post2
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : HST segs L HI) (LBo LB : list blk) (PKA : Z) (owned : list blk) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_CrtRelStmts ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VL,VHI,)Lh',(5.Vsegs,VL,VHI,)(1.(6.$7.)LLBo',(6.$7.)(8.(9.$0.R14.(:.(;.(<.O1:.O19.O18.O17.R13.R12.R11.O16.O15.R10.R?.R>.R=.R<.R;.R:.R9.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R8.R7.R6.R5.)O:.(=.O1:.)O9.(>.(2.&40.))R4.(?.Vsegs,))R3.))(8.(10.Vsegs,R4.)(8.(11.Vsegs,VL,R4.)(8.(12.Vsegs,R4.O3.(13.&40.O19.))(8.(14.O1.R3.)(8.(9.$15.(16.Vsegs,VL,VHI,R2.)(16.Vsegs,VL,VHI,O8.))(8.(17.Vsegs,VL,VHI,R2.(18.$7.R1.O6.)R4.R3.)(8.Pb,$7.P,(19.$7.R1.R2.)(19.$7.R2.O7.)(8.Pb,$7.P,(19.$7.R1.O7.)P,(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)O4.)))(19.$7.R3.R4.)(8.(1>.Vsegs,R4.O5.(1?.$20.(21.(22.&40.=))(1?.$20.(21.(22.&40.=))(23.$20.))))(8.(24.Vsegs,VL,(18.$7.R1.O6.)(13.&40.O19.)(1?.(1=.$15.$15.)(25.$15.$15.O5.(26.O5.+10.))(23.(1=.$15.$15.)))O2.R4.)Pb,$7.P,(19.$7.R1.R2.)(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)O4.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition pk_free_stmt2 (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_CrtRelStmts ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.Vsegs,VL,VHI,)PLBo,(6.$7.)PLB,(6.$7.)PPKA,$15.Pinfo,$15.Pctx,$15.Powned,(6.$7.)Plo,$15.P,(17.Vsegs,VL,VHI,R8.(18.$7.R7.R6.)R:.R9.)P,(1>.Vsegs,R;.R6.(1?.$20.(21.(22.&40.R5.))(1?.$20.(21.(22.&40.R4.))(23.$20.))))P,(9.$15.(28.R7.+8.)=)P,(29.Vsegs,VPK,R=.(18.$7.R:.R9.)R8.R7.R6.R5.)P,Pb,$7.P,(19.$7.R1.R7.)(19.$7.R2.R=.)P,(2:.(13.&40.R2?.)R:.)P,(2:.(26.R;.+10.)(16.Vsegs,VL,VHI,R>.))P,(12.Vsegs,R11.R8.(13.&40.R31.))P,(2:.(2;.VL,)R9.)P,(2:.R:.(2<.(2<.(13.&40.R33.)$2=.)(2>.VL,)))P,(9.$15.(28.(13.&40.R34.)+10.)=)P,(2:.(13.&40.R35.)(16.Vsegs,VL,VHI,R13.))P,(2:.(2?.VL,)(2;.VL,))P,(10.Vsegs,R17.)P,(11.Vsegs,VL,R18.)P,(9.(2.&40.)R37.(22.&40.(30.VL,)))P,(9.(2.&40.)R32.(22.&40.R15.))(31.Vsegs,R1:.(32.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R19.R18.R17.R16.R13.R12.R1;.R1:.)(;.(<.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(22.&40.O1.)R1<.(>.(2.&40.))R1;.(?.Vsegs,)))")
(* [comment removed for export] *).

  #[using="Type"] Lemma pk_free_stmt2_1 : forall ENTRY, pk_free_stmt2 ENTRY -> pk_free_stmt segs L HI PK ENTRY.
  Proof.
    intros ENTRY H2. unfold pk_free_stmt2, pk_free_stmt in *. intros.
    eapply aevtM_mono; [eapply H2; eassumption|].
    intros c (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & mo' & h' & LBo' & P).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', mo', h', LBo'. unfold pk_free_post. tauto.
  Qed.

  Definition x509_crt_free_post2
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (h : HST segs L HI) (LBo LB : list blk) (A : Z) (f : crt_own) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_CrtRelStmts ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.Vsegs,VL,VHI,)Lh',(5.Vsegs,VL,VHI,)(1.(6.$7.)LLBo',(6.$7.)(8.(9.$0.R14.(:.(;.(<.O1:.O19.O18.O17.R13.R12.R11.O16.O15.R10.R?.R>.R=.R<.R;.R:.R9.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R8.R7.R6.R5.)O:.(=.O1:.)O9.(>.(2.&40.))R4.(?.Vsegs,))R3.))(8.(10.Vsegs,R4.)(8.(11.Vsegs,VL,R4.)(8.(12.Vsegs,R4.O3.(13.&40.O19.))(8.(14.O1.R3.)(8.(9.$15.(16.Vsegs,VL,VHI,R2.)(16.Vsegs,VL,VHI,O8.))(8.(17.Vsegs,VL,VHI,R2.(18.$7.R1.O6.)R4.R3.)(8.Pb,$7.P,(19.$7.R1.R2.)(19.$7.R2.O7.)(8.Pb,$7.P,(19.$7.R1.O7.)P,(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)(33.O4.))))(19.$7.R3.R4.)(8.(34.Vsegs,R4.O5.)(8.(24.Vsegs,VL,(18.$7.R1.O6.)(13.&40.O19.)(1?.(1=.$15.$15.)(25.$15.$15.O5.(26.O5.$35.))(23.(1=.$15.$15.)))O2.R4.)P,(36.(9.$15.(37.O4.)=)(9.(2.&40.)(38.O4.)(22.&40.+1.)))Pb,$7.P,(19.$7.R1.R3.)(1:.(19.$15.(1;.$15.$15.R2.)(1<.(1=.$15.$15.)$15.(1;.$15.$15.)(33.O4.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition x509_crt_free_stmt2 (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_CrtRelStmts ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(27.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.Vsegs,VL,VHI,)PLBo,(6.$7.)PLB,(6.$7.)PA,$15.Pf,$39.Pj,$3:.Plo,$15.P,(17.Vsegs,VL,VHI,R7.(18.$7.R6.R5.)R9.R8.)P,(3;.Vsegs,VPK,R:.(18.$7.R7.R6.)R5.R4.R3.)P,Pb,$7.P,(19.$7.R1.(33.R6.))(19.$7.R2.R:.)P,(2:.(13.&40.R2<.)R7.)P,(2:.(26.R8.$35.)(16.Vsegs,VL,VHI,R;.))P,(12.Vsegs,R>.R6.(13.&40.R2>.))P,(2:.(2;.VL,)R7.)P,(2:.R8.(2<.(2<.(13.&40.R30.)$3<.)(2>.VL,)))P,(9.$15.(28.(13.&40.R31.)+10.)=)P,(2:.(13.&40.R32.)(16.Vsegs,VL,VHI,R10.))P,(2:.(2?.VL,)(2;.VL,))P,(10.Vsegs,R14.)P,(11.Vsegs,VL,R15.)P,(9.(2.&40.)R34.(22.&40.(30.VL,)))P,(9.(2.&40.)R2?.(22.&40.R12.))(31.Vsegs,R17.(3=.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.R13.R12.R10.R18.R17.)(;.(<.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(22.&40.O1.)R19.(>.(2.&40.))R18.(?.Vsegs,)))")
(* [comment removed for export] *).

  #[using="Type"] Lemma x509_crt_free_stmt2_1 : forall ENTRY, x509_crt_free_stmt2 ENTRY -> x509_crt_free_stmt segs L HI PK ENTRY.
  Proof.
    intros ENTRY H2. unfold x509_crt_free_stmt2, x509_crt_free_stmt in *. intros.
    eapply aevtM_mono; [eapply H2; eassumption|].
    intros c (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & mo' & h' & LBo' & P).
    exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m', mo', h', LBo'. unfold x509_crt_free_post. tauto.
  Qed.

End Stmts.
