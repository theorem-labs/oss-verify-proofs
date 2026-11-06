(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_stmtA_ng_sz () : Init.string Init.list := ["OSSVerify.KrLib.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibB.ARt.HM"; "OSSVerify.KrLib.LibB.ARt.HK"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Spec.MpiVal.mpd_sep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibB.ARt.fdata"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.B.A_mpi_stmtA.mpd_writableA"; "OSSVerify.KrLib.LibB.ARt.htop"; "OSSVerify.KrLib.Spec.Rep.LNull"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.B.A_mpi_stmtA_sz.arl_need_ecp"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.LibB.ARt.arl_tp"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.B.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibB.ARt.arl_AL"; "OSSVerify.KrLib.LibB.ARt.hcs"; "OSSVerify.KrLib.B.A_mpi_stmtA_sz.mpd_imgA"; "OSSVerify.KrLib.LibB.ARt.havol"; "OSSVerify.KrLib.LibB.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibB.ARt.hstkhi"; "OSSVerify.KrLib.B.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.LibB.ARt.hfr"; "OSSVerify.KrLib.LibB.ARt.FR_MAX"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "mpi_binop_ng_stmtA_sz"; "sub_abs_ng_Rsz"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.Spec.MpiVal.mpd_abs"; "Stdlib.ZArith.BinInt.Z.lt"; "add_mpi_ng_Rsz"; "sub_mpi_ng_Rsz"].


Definition sub_abs_ng_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  sub_abs_R LB dX dA dB r dX' /\ md_n dX' <= md_n dX.
Definition add_mpi_ng_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  add_mpi_R LB dX dA dB r dX' /\ md_n dX' <= md_n dX.
Definition sub_mpi_ng_Rsz (LB : list blk) (dX dA dB : mpd) (r : Z) (dX' : mpd) : Prop :=
  sub_mpi_R LB dX dA dB r dX' /\ md_n dX' <= md_n dX.

(* [comment removed for export] *)
Definition mpi_binop_ng_stmtA_sz (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) (STACK : Z)
    (PRE : mpd -> mpd -> mpd -> Prop) (Rr : list blk -> mpd -> mpd -> mpd -> Z -> mpd -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_ng_sz ()) "Ph,(0.O7.O6.O5.)PLB,(1.$2.)PLF,(1.$2.)Pra,(3.&40.)Psp,(3.&40.)Pgp,(3.&40.)Ptp,(3.&40.)Pt0,(3.&40.)Pt1,(3.&40.)Pt2,(3.&40.)Ps0,(3.&40.)Ps1,(3.&40.)Pa0,(3.&40.)Pa1,(3.&40.)Pa2,(3.&40.)Pa3,(3.&40.)Pa4,(3.&40.)Pa5,(3.&40.)Pa6,(3.&40.)Pa7,(3.&40.)Ps2,(3.&40.)Ps3,(3.&40.)Ps4,(3.&40.)Ps5,(3.&40.)Ps6,(3.&40.)Ps7,(3.&40.)Ps8,(3.&40.)Ps9,(3.&40.)Ps10,(3.&40.)Ps11,(3.&40.)Pt3,(3.&40.)Pt4,(3.&40.)Pt5,(3.&40.)Pt6,(3.&40.)PF,(4.&5.(3.&40.))Pfc,(3.&20.)Pm,P,(3.&40.)(5.(3.&8.))Pmo,$6.PdX,$7.PdA,$7.PdB,$7.Plo,$8.Pd,$8.P,(9.O7.O6.O5.R2;.R2:.R29.R7.)P,(:.O7.O6.O5.R2<.R7.)P,(;.O7.R9.R2<.R7.)P,(;.O7.R:.R2=.R7.)P,(;.O7.R;.R2>.R7.)P,(<.R:.R9.)P,(<.R;.R9.)P,(<.R;.R:.)P,(=.(>.$?.(10.R=.)$11.))P,A3.O2.R>.R=.R<.P,(12.R?.R>.R<.(13.&40.R31.))P,(12.R10.R>.R=.(13.&40.R32.))P,(14.(15.O6.)(16.$2.R36.(17.R35.))R>.(18.R10.)+10.)P,P,(>.$?.(10.R11.)$19.)(14.(15.O6.)(16.$2.R38.(17.R37.))R10.(1:.R12.)(1;.+4.(1<.R12.)))P,(14.(15.O6.)(16.$2.R38.(17.R37.))R10.(18.R11.)+10.)P,P,(>.$?.(10.R12.)$19.)(14.(15.O6.)(16.$2.R3:.(17.R39.))R12.(1:.R13.)(1;.+4.(1<.R13.)))P,(1=.O6.R3:.R39.(13.&40.R37.)(1>.O7.O6.O5.R3;.)R15.)P,P,(=.(>.$?.(10.R16.)$1?.))(20.(21.(22.(1:.R17.)(1;.+4.(1<.R17.)))R14.)(21.(13.&40.R39.)(1:.R17.)))P,(23.O7.R19.R14.(13.&40.R39.))P,(21.(24.O6.)R15.)P,(21.R16.(25.(25.(13.&40.R3;.)O3.)(26.O6.)))P,(21.(13.&40.R3<.)(1>.O7.O6.O5.R40.))P,(>.$8.(27.(13.&40.R3=.)+10.)=)P,(>.(3.&40.)R3<.(28.&40.(29.O6.)))P,(2:.O7.R1?.)P,(>.$8.(27.(13.&40.R41.)+2.)=)P,(2;.O7.(2<.O6.)(2=.O7.O6.O5.R45.)R21.R1?.)P,(2;.O7.(2<.O6.)(2=.O7.O6.O5.R46.)R22.R1?.)P,(2;.O7.(2<.O6.)(2=.O7.O6.O5.R47.)R23.R1?.)P,(2>.R21.)P,(2>.R21.)P,(21.(22.(2?.O7.O6.O5.R4:.)=)$30.)P,(31.O7.R27.(24.O6.)(32.O7.O6.O5.R4;.)(13.&40.R41.)(13.&40.R47.)R21.)P,(33.O6.(18.R26.)+10.R22.)P,(33.O6.(18.R26.)+10.R23.)P,(33.O6.(18.R26.)+10.R24.)P,(21.(22.(34.O7.O6.O5.R4?.)=)$35.)P,(>.(3.&40.)R44.(28.&40.(18.R2:.)))P,(>.(3.&40.)R44.(28.&40.(18.R2:.)))P,(>.(3.&40.)R44.(28.&40.(18.R2:.)))(36.O7.(37.O7.O6.O5.R50.R4?.R4>.R4=.R49.R48.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R31.R30.R53.R52.R51.R2=.A4.O1.R52.R2=.R2<.R2;.==R2:.R2?.R2>.)(38.(39.(3:.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.)R31.(28.&40.O4.)R30.(3;.(3.&40.))R2?.(3<.O7.))R2>.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition mpi_sub_abs_ng_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_ng_sz ()) "(3=.O4.O3.O2.O1.+>0.LdX,$7.LdA,$7.LdB,$7.(21.(1<.R2.)(1<.R3.))$3>.)")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition mpi_add_mpi_ng_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_ng_sz ()) "(3=.O4.O3.O2.O1.+170.LdX,$7.LdA,$7.LdB,$7.(3?.(>.$8.(40.R1.)(41.(40.R2.)))(3?.P,(21.(42.R1.)(42.R2.))(21.(1<.R3.)(1<.R4.))P,(43.(42.R2.)(42.R1.))(21.(1<.R2.)(1<.R4.))))$44.)")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition mpi_sub_mpi_ng_stmtA_sz segs R HIA ENTRY := ltac2:(CDefT.buildp (gd_tbl_A_mpi_stmtA_ng_sz ()) "(3=.O4.O3.O2.O1.+170.LdX,$7.LdA,$7.LdB,$7.(3?.(>.$8.(40.R1.)(40.R2.))(3?.P,(21.(42.R1.)(42.R2.))(21.(1<.R3.)(1<.R4.))P,(43.(42.R2.)(42.R1.))(21.(1<.R2.)(1<.R4.))))$45.)")
(* [comment removed for export] *).
