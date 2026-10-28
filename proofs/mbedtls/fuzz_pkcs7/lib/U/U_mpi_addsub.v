(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_addsub () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "mpd_writable"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "mpi_binop_post"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_abs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "MBEDTLS_ERR_MPI_ALLOC_FAILED"; "binop_keep"; "MBEDTLS_ERR_MPI_NEGATIVE_VALUE"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"].


Definition U_MPI_ADD_ABS : Z := 0x20494.
Definition U_MPI_SUB_ABS : Z := 0x2078c.
Definition U_ADD_SUB_MPI : Z := 0x20a04.
Definition U_MPI_ADD_MPI : Z := 0x209fc.
Definition U_MPI_SUB_MPI : Z := 0x20b04.
Definition U_MPI_ADD_INT : Z := 0x1fd60.
Definition U_MPI_SUB_INT : Z := 0x20b0c.

Definition MBEDTLS_ERR_MPI_ALLOC_FAILED : Z := -16.
Definition MBEDTLS_ERR_MPI_NEGATIVE_VALUE : Z := -10.

(* [comment removed for export] *)
Notation MPI_ADD_ABS_STACK := 176 (only parsing).
Notation MPI_SUB_ABS_STACK := 160 (only parsing).
Notation MPI_ADD_SUB_STACK := 224 (only parsing).
Notation MPI_ADD_INT_STACK := 256 (only parsing).

(* [comment removed for export] *)
Definition mpd_writable (L : heap_layout) (LB : list blk) (SP top : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(1.O5.O4.O3.O2.(2.O1.)+10.)(0.Pa,$3.P,(0.(4.(2.O1.)R1.)(5.R1.(6.(2.O1.)+10.)))P,(0.(4.(7.O5.)R2.)(5.R2.(8.O5.)))(9.O5.R3.)P,(:.$;.(<.O1.)$=.)(>.(4.(6.(2.O1.)+10.)(?.O1.))(4.(6.(?.O1.)(10.+4.(11.O1.)))(2.O1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_binop_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (dX : mpd) (R : Z -> mpd -> Prop) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "Lc,$12.(13.(14.&40.)Lt0,(14.&40.)(13.(14.&40.)Lt1,(14.&40.)(13.(14.&40.)Lt2,(14.&40.)(13.(14.&40.)La1,(14.&40.)(13.(14.&40.)La2,(14.&40.)(13.(14.&40.)La3,(14.&40.)(13.(14.&40.)La4,(14.&40.)(13.(14.&40.)La5,(14.&40.)(13.(14.&40.)La6,(14.&40.)(13.(14.&40.)La7,(14.&40.)(13.(14.&40.)Lt3,(14.&40.)(13.(14.&40.)Lt4,(14.&40.)(13.(14.&40.)Lt5,(14.&40.)(13.(14.&40.)Lt6,(14.&40.)(13.P,(14.&40.)(15.(14.&8.))Lm',P,(14.&40.)(15.(14.&8.))(13.$16.Lmo',$16.(13.(17.O1<.O1;.O1:.)Lh',(17.O1<.O1;.O1:.)(13.(18.$19.)LLB',(18.$19.)(13.$1:.LdX',$1:.(13.$3.Lr,$3.(0.(:.$12.R15.(1;.(1<.(1=.O19.O18.O17.O16.R14.R13.R12.O15.O14.(1>.&40.R1.)R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(1?.O19.)O8.(20.(14.&40.))R6.(21.O1<.))R5.))(0.(22.O1<.R6.)(0.(23.O1<.R6.O3.(24.&40.O18.))(0.(25.O1.R5.)(0.(:.$3.(26.O1<.O1;.O1:.R4.)(26.O1<.O1;.O1:.O7.))(0.(27.O1<.O1;.O1:.R4.R3.R6.R5.)(0.(28.O1<.R6.R3.R2.)(0.(29.O6.O5.R3.R2.)(0.(2:.O1<.O1;.O6.(24.&40.O18.)(2;.O5.)O2.R6.)(0.(2<.O1<.O1;.R6.)A2.O4.R1.R2.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition opnd_sep (dX d : mpd) (lo SP : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.P,(2=.(:.$;.(<.O3.)$2>.))(>.(4.(6.(2.O4.)+10.)(?.O3.))(4.(6.(?.O3.)(10.+4.(11.O3.)))(2.O4.)))(0.P,(:.$;.(<.O4.)$=.)(>.(4.(6.(2.O3.)+10.)(?.O4.))(4.(6.(?.O4.)(10.+4.(11.O4.)))(2.O3.)))(0.(>.(:.$1:.O4.O3.)(>.(2=.(:.$;.(<.O4.)$=.))(>.(:.$;.(<.O3.)$2>.)(>.(4.(6.(?.O4.)(10.+4.(11.O4.)))(?.O3.))(4.(6.(?.O3.)(10.+4.(11.O3.)))(?.O4.))))))(0.(>.(4.(6.(2.O3.)+10.)O2.)(4.O1.(2.O3.)))P,(2=.(:.$;.(<.O3.)$2>.))(>.(4.(6.(?.O3.)(10.+4.(11.O3.)))O2.)(4.O1.(?.O3.)))))))")
(* [comment removed for export] *).                            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mpi_binop_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF STACK : Z)
    (R : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "Pra,(14.&40.)Psp,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa0,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PF,(2?.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(15.(14.&8.))Pmo,$16.Ph,(17.O7.O6.O5.)PLB,(18.$19.)PdX,$1:.PdA,$1:.PdB,$1:.Plo,$3.P,(27.O7.O6.O5.R6.R5.R8.R7.)P,(28.O7.R9.R6.R5.)P,(28.O7.R:.R7.R5.)P,(28.O7.R;.R8.R5.)P,(30.R8.R7.)P,(30.R9.R7.)P,(30.R9.R8.)P,(2=.(:.$;.(<.R;.)$31.))P,(32.R<.R;.R9.(24.&40.R30.))P,(32.R=.R;.R:.(24.&40.R31.))P,(33.O6.R?.R;.(2.R=.)+10.)P,P,(:.$;.(<.R>.)$=.)(33.O6.R11.R=.(?.R?.)(10.+4.(11.R?.)))P,(33.O6.R11.R=.(2.R>.)+10.)P,P,(:.$;.(<.R?.)$=.)(33.O6.R13.R?.(?.R10.)(10.+4.(11.R10.)))P,(34.O6.R13.(24.&40.R36.)(26.O7.O6.O5.R14.)R12.)P,P,(2=.(:.$;.(<.R13.)$2>.))(>.(4.(6.(?.R14.)(10.+4.(11.R14.)))R11.)(4.(24.&40.R38.)(?.R14.)))P,(23.O7.R18.R11.(24.&40.R38.))P,(4.R12.(35.(35.(24.&40.R39.)O2.)(36.O6.)))P,(4.(37.O6.)R13.)P,(4.(24.&40.R3;.)(26.O7.O6.O5.R19.))P,(:.$3.(38.(24.&40.R3<.)+10.)=)P,(4.(8.O6.)(37.O6.))P,(:.(14.&40.)R3<.(1>.&40.(39.O6.)))P,(22.O7.R1?.)P,(2<.O7.O6.R20.)P,(3:.O6.O3.+8.)P,(:.(14.&40.)R3:.(1>.&40.(2.R1>.)))P,(:.(14.&40.)R3:.(1>.&40.(2.R1>.)))P,(:.(14.&40.)R3:.(1>.&40.(2.R1>.)))(3;.O7.R24.(3<.O7.O6.O5.R46.R45.R44.R43.R3?.R3>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R23.R22.R21.A4.O1.R22.R21.R20.R1?.R1>.R25.R24.)(1<.(1=.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(1>.&40.O4.)R26.(20.(14.&40.))R25.(21.O7.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition binop_keep (LB : list blk) (dX dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(:.$3.(2.O1.)(2.O2.))(0.(:.(14.&40.)(3=.O1.)(3=.O2.))(0.Pb,$19.P,(3>.$19.R1.(3?.O1.))(>.(3>.$19.R2.(3?.O2.))(2=.(3>.$19.R2.O3.)))(4.(11.O2.)(11.O1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition add_abs_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(0.(:.$3.(40.O1.)(6.(41.O4.)(41.O3.)))(:.$3.(42.O1.)+1.)))(:.$3.O2.$43.))(44.O6.O5.O1.))")
(* [comment removed for export] *).
Definition sub_abs_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(0.(:.$3.(40.O1.)(35.(41.O4.)(41.O3.)))(:.$3.(42.O1.)+1.)))(>.(:.$3.O2.$43.)(0.(:.$3.O2.$45.)(5.(41.O4.)(41.O3.)))))(44.O6.O5.O1.))")
(* [comment removed for export] *).
Definition add_mpi_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(:.$3.(40.O1.)(6.(40.O4.)(40.O3.))))(:.$3.O2.$43.))(44.O6.O5.O1.))")
(* [comment removed for export] *).
Definition sub_mpi_R (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(:.$3.(40.O1.)(35.(40.O4.)(40.O3.))))(:.$3.O2.$43.))(44.O6.O5.O1.))")
(* [comment removed for export] *).

Definition mpi_add_abs_stmt segs L HI ENTRY MSF := mpi_binop_stmt segs L HI ENTRY MSF MPI_ADD_ABS_STACK add_abs_R.
Definition mpi_sub_abs_stmt segs L HI ENTRY MSF := mpi_binop_stmt segs L HI ENTRY MSF MPI_SUB_ABS_STACK sub_abs_R.
Definition mpi_add_mpi_stmt segs L HI ENTRY MSF := mpi_binop_stmt segs L HI ENTRY MSF MPI_ADD_SUB_STACK add_mpi_R.
Definition mpi_sub_mpi_stmt segs L HI ENTRY MSF := mpi_binop_stmt segs L HI ENTRY MSF MPI_ADD_SUB_STACK sub_mpi_R.
(* [comment removed for export] *)
Definition add_sub_mpi_R (flip : Z) (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(:.$3.(40.O1.)(6.(40.O4.)(10.O7.(40.O3.)))))(:.$3.O2.$43.))(44.O6.O5.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_intop_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z)
    (R : list blk -> mpd -> mpd -> Z -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "Pra,(14.&40.)Psp,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa0,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PF,(2?.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(15.(14.&8.))Pmo,$16.Ph,(17.O6.O5.O4.)PLB,(18.$19.)PdX,$1:.PdA,$1:.Pb,$3.Plo,$3.P,(27.O6.O5.O4.R6.R5.R8.R7.)P,(28.O6.R9.R6.R5.)P,(28.O6.R:.R7.R5.)P,(30.R7.R6.)P,(2=.(:.$;.(<.R8.)$31.))P,(32.R9.R8.R6.(24.&40.R2=.))P,(33.O5.R;.R7.(2.R9.)+10.)P,P,(:.$;.(<.R:.)$=.)(33.O5.R=.R9.(?.R;.)(10.+4.(11.R;.)))P,(34.O5.R=.(24.&40.R30.)(26.O6.O5.O4.R>.)R<.)P,(0.(4.(46.(47.+2.+1?.))R;.)(5.R;.(47.+2.+1?.)))P,P,(2=.(:.$;.(<.R>.)$2>.))(>.(4.(6.(?.R?.)(10.+4.(11.R?.)))R<.)(4.(24.&40.R33.)(?.R?.)))P,(23.O6.R13.R<.(24.&40.R33.))P,(4.R=.(35.(35.(24.&40.R34.)+100.)(36.O5.)))P,(4.(37.O5.)R>.)P,(4.(24.&40.R36.)(26.O6.O5.O4.R14.))P,(:.$3.(38.(24.&40.R37.)+10.)=)P,(4.(8.O5.)(37.O5.))P,(:.(14.&40.)R37.(1>.&40.(39.O5.)))P,(22.O6.R1:.)P,(2<.O6.O5.R1;.)P,(3:.O5.O2.+8.)P,(:.(14.&40.)R35.(1>.&40.(2.R19.)))P,(:.(14.&40.)R35.(1>.&40.(2.R19.)))P,(:.(14.&40.)R35.(1>.&40.R19.))(3;.O6.R1?.(3<.O6.O5.O4.R41.R40.R3?.R3>.R3:.R39.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R22.R21.R1>.R1=.R1<.A4.O1.R1=.R1<.R1;.R1:.R19.R20.R1?.)(1<.(1=.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R22.(1>.&40.O3.)R21.(20.(14.&40.))R20.(21.O6.)))")
(* [comment removed for export] *).
Definition add_int_R (LB : list blk) (dX dA : mpd) (b r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(:.$3.(40.O1.)(6.(40.O4.)O3.)))(:.$3.O2.$43.))(44.O6.O5.O1.))")
(* [comment removed for export] *).
Definition sub_int_R (LB : list blk) (dX dA : mpd) (b r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_addsub ()) "(0.(>.(0.(:.$3.O2.=)(:.$3.(40.O1.)(35.(40.O4.)O3.)))(:.$3.O2.$43.))(44.O6.O5.O1.))")
(* [comment removed for export] *).
Definition mpi_add_int_stmt segs L HI ENTRY MSF := mpi_intop_stmt segs L HI ENTRY MSF add_int_R.
Definition mpi_sub_int_stmt segs L HI ENTRY MSF := mpi_intop_stmt segs L HI ENTRY MSF sub_int_R.

(* [comment removed for export] *)
