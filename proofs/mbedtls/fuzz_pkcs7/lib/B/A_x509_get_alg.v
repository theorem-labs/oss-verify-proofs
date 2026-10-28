(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_asn1_get_alg_A P_x509_get_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_platform_zeroize A_asn1_get_alg_A A_asn1_get_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxA_sums. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import LxConv_getlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P009904bb0eb69120 0 2 2 1 4 1P02cb35c021c1840a 0 4 0 1 37 1 51 1 52 1P02eaf8644a913193 0 5 0 1 38 1 48 1 51 1 52 1P035889daef466024 0 4 0 1 2 1 55 1 56 1P049edde5de70806c 0 4 0 1 3 1 54 1 55 1P06e553abde38145b 2 40 1 1 8 3 2 1 54 1 55 1 6 0 2 40 2 50 2 53 2 56 2 57 16 1 1 8 3 1 1 53 1 56 1 4 0 1 54 1 55 1 57 8P0754ba35b82a5dd5 0 4 1 1 3 1 54 1 55 1P08b921e1cdac693d 0 5 0 1 59 1 69 1 74 1 75 1P0933821e4c7a3643 0 2 0 1 2 1P0ae4e638641aa8b9 2 41 1 1 8 3 2 1 54 1 55 1 6 0 2 40 2 50 2 53 2 56 2 57 16 1 1 8 3 1 1 53 1 56 1 4 0 1 54 1 55 1 57 8P0c966ece011a4147 0 5 0 1 38 1 48 1 51 1 52 1P0d3431a69019a028 0 4 1 1 3 1 54 1 55 1P0e13b3b19e8da548 0 4 0 16 4 16 51 16 52 16P0fbdde2626b64376 3 38 0 2 1 1 2 1 0 6 0 1 3 1 41 1 51 1 54 1 55 1 0 4 0 1 2 1 54 1 55 1P11fde53751da3867 0 2 0 1 21 1P12cf88a054baa4d9 1 1 8 3 0 1 54 1 55 1 6 2 1 40 1 50 1 53 1 56 1 57 8P14542af8eb7d09d0 0 2 1 1 3 1P15a21945a620ceff 0 2 0 1 47 1P16998fafbe7f1537 0 2 0 1 20 1P172e9ec7ded4f61f 1 1 8 3 0 1 54 1 55 1 6 2 1 40 1 50 1 53 1 56 1 57 8P17fdfd445d6849bd 0 2 0 1 1 1P18bb297efe3461d1 1 1 8 3 1 1 54 1 55 1 4 2 2 53 2 56 2 57 16P18f648a0e68ddf9c 1 1 8 2 42 1 52 1 3 0 1 51 1 53 8P1973a7497ef3e787 0 4 0 1 1 1 52 1 53 1P1a169be1908eea90 0 2 0 1 45 1P1c1ae141d15fdda4 0 5 0 1 38 1 48 1 51 1 52 1P1ca749936cc2797c 0 2 0 1 46 1P1d5d0a95b51d9ff0 0 4 0 1 2 1 55 1 56 1P20e0f78c4457a416 2 39 1 1 8 3 2 1 54 1 55 1 6 0 2 40 2 50 2 53 2 56 2 57 16 1 1 8 3 1 1 53 1 56 1 4 0 1 54 1 55 1 57 8P20e28a4aa15a2ed0 0 2 0 1 40 1P217f97dfd9197cc9 0 6 0 1 38 1 39 1 48 1 51 1 52 1P225a9714572d699c 0 4 0 1 3 1 54 1 55 1P226eaf48d4d0d03a 1 1 8 2 41 1 52 1 3 0 1 51 1 53 8P24be6e2f20f3edfc 1 1 16 2 0 1 51 1 3 5 1 52 1 53 16P255690b5869c6263 1 1 8 2 43 1 52 1 3 0 1 51 1 53 8P27e11faf93ad3db1 1 1 8 3 1 1 54 1 55 1 4 2 2 53 2 56 2 57 16P2a1072f04b09b262 0 2 0 1 39 1P2aa1a7086a12a7ba 0 4 0 1 37 1 51 1 52 1P2ad4e0260fcd2605 0 5 0 1 59 1 69 1 74 1 75 1P2b01443a157790e7 0 4 0 1 3 1 54 1 55 1P2ca3d14151ded09c 1 1 8 3 1 1 53 1 56 1 4 2 2 54 2 55 2 57 16P2d328fd234c1d293 0 4 1 1 3 1 54 1 55 1P2e43fc8305029982 1 1 8 3 0 1 54 1 55 1 6 2 1 40 1 50 1 53 1 56 1 57 8P2e52d8fcdc10f96c 0 4 0 1 2 1 55 1 56 1P2e5371cde3f360b2 0 2 2 1 4 1P2f58bf8a63addd9e 0 2 0 1 44 1P2fff6ca9e53f972e 0 4 0 1 3 1 54 1 55 1P30be2270314cf601 0 4 0 1 38 1 51 1 52 1P3124bff6b22c511b 0 5 0 1 59 1 69 1 74 1 75 1P319cfa29520440f8 0 2 2 1 4 1P32ec1f33852129f8 0 2 0 1 1 1P335967a8520d524f 1 1 8 3 1 1 54 1 55 1 4 2 2 53 2 56 2 57 16P3404af7366be7e09 1 1 8 3 1 1 53 1 56 1 4 2 2 54 2 55 2 57 16P340eff54634c9308 1 1 8 3 1 1 53 1 56 1 4 2 2 54 2 55 2 57 16P359d029151cd9224 0 5 0 1 38 1 48 1 51 1 52 1P3807c374ff04c082 0 5 0 1 38 1 48 1 51 1 52 1P39af13bea1836a41 0 2 0 1 39 1P39b41ee168cc5753 0 4 0 1 37 1 51 1 52 1P3d6e08888144e017 0 5 0 1 59 1 69 1 74 1 75 1P3dd6b0c576c5167d 0 2 2 1 4 1P3e1c9d44841fdb34 0 2 0 1 21 1P3e6ec58d419272ec 0 5 0 1 38 1 48 1 51 1 52 1P3e9d0d5e262aedf1 0 2 0 1 20 1N00c999aceb453ce2N01f783e4da3f9150N0451842fb97c5e98N04a30c10e36371b6N04f658a659b880fbN054fdbd2ace604a5N0554e401ca8822fcN06dcb1e10cf01e8fN075edb40373c71f5N079f2e58d7ec097bN0d98a57bfdb77be7N0e3183816486560aN0edc398c267cbe45N0f92c4c672056591N10328c71d139ff1eN121e16b9809fe884N157eda35e78654f3N16b123bc4a4d3d7aN17edac2bcf34b54cN17f61d9878c2ee0bN1a67d9a814923fd1N1acf87b65b59770dN1c5bc8f094b54908N1d954a0bb3b5f960N1eda8ac50f622e52N207630c88b7ca9a5N20a0a115f8c67630N20e75dece694da09N229cbaf60cc4811dN2341e5a90a75172cN23f63a0686cc5208N24481d599e3d8583N27214a049a362d84N277b319e6e603f75N295c31dbcce64007N2e00dbda1d74a653N31218b07073bdc29N3226ca0abd20b883N3755636659783267N38dbb7e0b02aa84eN39e1374de4aca96aN3a23901caae6678eN3e044d5f8f8192caN3eab9762305fd843N3f7e7a76a2b6dae8"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_x509_get_alg () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "x509_get_alg_postA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_memset_i"; "RocqVerifyHarness.AgentSubmission.B.A_platform_zeroize.A_WRAP_MEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_rtc"; "RocqVerifyHarness.AgentSubmission.B.AImgRT.asan_rtc"; "x509_get_alg_stmtA"; "A_X509_GET_ALG"].


Definition A_X509_GET_ALG : Z := 0x0ac114.
Notation X509_GET_ALG_STACK_A := 112 (only parsing).   (* [comment removed for export] *)

Definition x509_get_alg_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP ALG PAR P END BUF lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_alg ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Latag,(2.&40.)(1.(2.&40.)Lapad,(2.&40.)(1.(2.&40.)Lalen,(2.&40.)(1.(2.&40.)Lapw,(2.&40.)(1.(2.&40.)Lptag,(2.&40.)(1.(2.&40.)Lppad,(2.&40.)(1.(2.&40.)Lplen,(2.&40.)(1.(2.&40.)Lppw,(2.&40.)(5.(6.$0.R1;.(7.(8.O1:.O19.O18.O17.R1:.R19.R18.O16.O15.R17.R16.R15.R14.R13.R12.R11.R10.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R?.R>.R=.R<.)O:.(9.O1:.)O9.(:.(2.&40.))R;.(;.O20.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O8.(10.O8.+8.))(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+18.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.O2.(11.&40.O19.))(12.(>.$4.$4.))))))O1.R;.)(5.(13.O20.O1.R;.)(5.(14.O20.R;.)(5.(6.(2.&40.)R17.(15.&40.R:.))(5.(5.(16.-3000.R:.)(17.R:.=))(5.(18.O20.R;.O8.(=.$19.(1:.(15.&40.R9.))(12.$19.)))(5.(18.O20.R;.O7.(=.$19.(1;.R8.)(=.$19.(1;.R7.)(=.$19.(1:.R6.)(=.$19.(1:.R5.)(12.$19.))))))(5.(18.O20.R;.O6.(=.$19.(1;.R4.)(=.$19.(1;.R3.)(=.$19.(1:.R2.)(=.$19.(1:.R1.)(12.$19.))))))(5.(1<.O20.R;.O2.(11.&40.O19.))(5.(1=.O20.O1?.O1>.O1=.O1<.O1;.R;.)(5.(5.(17.O5.R9.)(17.R9.O4.))P,(6.$4.R:.=)(1.$4.Lap,$4.(1.$4.Lpp,$4.(5.(6.(2.&40.)R8.(15.&40.R2.))(5.(6.(2.&40.)R4.(15.&40.R1.))(5.(17.O3.R2.)(5.(17.(10.R2.(11.&40.R9.))R<.)(1>.(5.(6.$4.R1.=)(6.$4.(11.&40.R5.)=))(5.(17.O3.R1.)(6.$4.(10.R1.(11.&40.R5.))R<.)))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_alg_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_get_alg ()) "Ph,(1?.O4.O3.O2.)PLB,(20.$21.)PLF,(20.$21.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PPP,$4.PALG,$4.PPAR,$4.PP,$4.PEND,$4.PBUF,$4.Plo,$4.Pbs,(20.(2.&8.))Patag,(2.&40.)Papad,(2.&40.)Palen,(2.&40.)Papw,(2.&40.)Pptag,(2.&40.)Pppad,(2.&40.)Pplen,(2.&40.)Pppw,(2.&40.)P,(1=.O4.O3.O2.R35.R34.R33.R11.)P,(18.O4.R12.R11.(=.$19.(1:.(15.&40.R>.))(12.$19.)))P,(18.O4.R13.R11.(=.$19.(1;.R:.)(=.$19.(1;.R9.)(=.$19.(1:.R8.)(=.$19.(1:.R7.)(12.$19.))))))P,(18.O4.R14.R11.(=.$19.(1;.R7.)(=.$19.(1;.R6.)(=.$19.(1:.R5.)(=.$19.(1:.R4.)(12.$19.))))))P,(23.O4.R15.R?.R=.)P,(17.R10.R12.)P,(17.R13.R12.)P,(17.R13.(10.R12.(24.(25.(2.&8.)R10.))))P,(16.(10.R13.(24.(25.(2.&8.)R11.)))(26.+2.+3?.))P,(1>.(17.(10.R19.+8.)R18.)(17.(10.R18.+18.)R19.))P,(1>.(17.(10.R1:.+8.)R18.)(17.(10.R18.+18.)R1:.))P,(1>.(17.(10.R1:.+18.)R19.)(17.(10.R19.+18.)R1:.))P,(1>.(6.$4.(24.(25.(2.&8.)R15.))=)(1>.(17.(10.R1<.+8.)R17.)(17.(10.R17.(24.(25.(2.&8.)R15.)))R1<.)))P,(1>.(6.$4.(24.(25.(2.&8.)R16.))=)(1>.(17.(10.R1<.+18.)R18.)(17.(10.R18.(24.(25.(2.&8.)R16.)))R1<.)))P,(1>.(6.$4.(24.(25.(2.&8.)R17.))=)(1>.(17.(10.R1<.+18.)R19.)(17.(10.R19.(24.(25.(2.&8.)R17.)))R1<.)))P,(6.$4.(27.R1?.+8.)=)P,(6.$4.(27.R1?.+8.)=)P,(6.$4.(27.R1?.+8.)=)P,(16.=R22.)P,(16.=R22.)P,(16.=R22.)P,(16.=R20.)P,(1<.O4.R27.R20.(11.&40.R47.))P,(17.(28.O3.)R21.)P,(17.R22.(29.(29.(11.&40.R49.)+70.)(2:.O3.)))P,(17.(11.&40.R4:.)(2;.O4.O3.O2.R4>.))P,(6.$4.(27.(11.&40.R4;.)+10.)=)P,(1>.(17.(10.R2;.+8.)R25.)(17.(11.&40.R4<.)R2;.))P,(1>.(17.(10.R2;.+18.)R26.)(17.(11.&40.R4=.)R2;.))P,(1>.(17.(10.R2;.+18.)R27.)(17.(11.&40.R4>.)R2;.))P,(1>.(6.$4.(24.(25.(2.&8.)R27.))=)(1>.(17.(10.R29.(24.(25.(2.&8.)R27.)))R28.)(17.(11.&40.R4?.)R29.)))P,(2<.(2=.O3.)(2>.$21.R53.(2?.R52.))(28.O3.)(2;.O4.O3.O2.R54.)R2?.+8.)P,(2<.(2=.O3.)(2>.$21.R54.(2?.R53.))(28.O3.)(2;.O4.O3.O2.R55.)R2?.+18.)P,(2<.(2=.O3.)(2>.$21.R55.(2?.R54.))(28.O3.)(2;.O4.O3.O2.R56.)R2?.+18.)P,(14.O4.R33.)P,(30.O4.(31.O3.)(32.O4.O3.O2.R58.)R34.R33.+8.)P,(30.O4.(31.O3.)(32.O4.O3.O2.R59.)R35.R33.+18.)P,(30.O4.(31.O3.)(32.O4.O3.O2.R5:.)R36.R33.+18.)P,(30.O4.(31.O3.)(32.O4.O3.O2.R5;.)R37.R31.(24.(25.(2.&8.)R2?.)))P,(30.O4.(31.O3.)(32.O4.O3.O2.R5<.)R38.(29.(11.&40.R58.)+58.)+8.)P,(6.(2.&40.)R51.(15.&40.R38.))P,(6.(2.&40.)R51.(15.&40.R35.))P,(6.(2.&40.)R51.(15.&40.R39.))P,(6.(2.&40.)R51.(15.&40.R39.))(33.O4.(31.O3.)(32.O4.O3.O2.R61.)(34.O4.O3.O2.R61.R60.R5?.R5>.R5=.R5<.R5;.R57.R56.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R3?.R3>.R3<.R3;.R3:.R39.R38.R37.R36.R3=.)(7.(8.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.)R3?.(15.&40.O1.)R3>.(:.(2.&40.))R3=.(;.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis HALGS : asn1_get_alg_stmtA asegs R HIA A_ASN1_GET_ALG.
  Hypothesis NEED0 : 0 <= arl_need_amem R.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00Y0@D10649662601.116D25837644109.118D38723547381.117D46807815276.116D560907437.119  D60299481098.118D62011770191.119D68714451741.117L13345552802.147L20433961190.113L20674044696.140L23687509038.142L28693905736.144L29428324939.5  L30095795534.140L31569658026.142L34633694313.2  L35653441506.7  L35654466029.2  L4294851542.2   L43059266230.111L46277880743.2  L48403999841.142L48410235227.144L48410595544.147L54505774524.140L55880402042.140L5727102411.142 L59314873579.2  L59314873579.3  L59314873579.4  L59314873579.5  L59314988138.1  L59314988138.142L59314988138.2  L60098763854.3  L64376777856.141L65566128912.2  L65886971467.142L67797337510.147L68095078813.2  00000B00T00f01801R01d02802J03^04>04Y05805905K05f06C06D06\06]06^07]07^07_08U09K09f0:A0:[0:\0:]0:^0:_0:`0;L0;M0;W0<50<60<P0=L0=MS2sp2PP3ALG3PAR2bsS2sp2PP3ALG3PAR2bsS2sp2PP3ALG3PAR2bsS2sp2PP3ALG3PAR2bsS1R3HIA1h2sp2PP3ALG3PAR2bsS2sp2PP3ALG3PAR2bsS1R2sp2PP3ALG3PAR2bsS2sp2PP3ALG3PAR2bsS2sp2PP3ALG3PAR3BUF2bs3NZ13NZ23NZ33SPR3lxv4lxv04lxv74lxv83H143H153H163H173H213H232R0S2sp2PP3ALG3PAR2bs3PPB4ALGB4PARBS2sp2PP3ALG3PAR2bs4lxv73H22S2sp2PP3ALG3PAR3END2bs4lxv03H36FS1R2lo3LOS3ALO3ACPS2sp2PP3ALG3PAR2bs4lxv33H31S2sp2PP3ALG3PAR1P2bs4lxv03H37FS1R3HIA1h2sp2lo3TOP4HTOPFFS1R5NEED02sp2PP3ALG3PAR2lo2bs3NZ13NZ23NZ33SLO3SPR3PPB4ALGB4PARBFFS2sp2PP3ALG3PAR3BUF2bs3NZ13NZ23NZ33SPR3lxv4lxv43H192R0S2sp2PP3ALG3PAR3BUF2bs3NZ13NZ23NZ33SPR3lxv4lxv43H192R0S2sp2PP3ALG3PAR2bs4lxv33H30S2sp2PP3ALG3PAR2bs4lxv73H23S2sp2PP3ALG3PAR2bs3lxv3H38FFFFFS2sp2PP3ALG3PAR2bs3NZ13NZ23NZ33SPR3lxv3H381GFS1R2lo3LOSS2sp2PP3ALG3PAR2bs3lxv3H383H39FS2sp2PP3ALG3PAR2bs3lxv3H39S2sp2PP3ALG3PAR2bs3NZ13NZ23NZ33SPR3lxv4lxv04lxv34lxv43H182R0F". (* [comment removed for export] *)
  Lemma A_x509_get_alg_walk : x509_get_alg_stmtA asegs R HIA A_X509_GET_ALG.
  Proof.
  (* [comment removed for export] *)
  pose proof HALGS as SPA.
  unfold asn1_get_alg_stmtA, A_ASN1_GET_ALG in SPA.
  unfold x509_get_alg_stmtA, A_X509_GET_ALG.
  intros until ppw.
  intros HH HPP HALG HPAR HBUF B1 B2 B3 B4 D1 D1b D1c D2 D3 D3b AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 ST LOS SLO TOP SPA16
    DS1 DS2 DS3 DS4 CW1 CW2 CW3 MI OPP OALG OPAR OBUF OLS -> -> -> ->.
  pose proof (hcs_ok asegs R HIA h) as CSOK.
  pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'.
  unfold al_wf in ALWF'.
  pose proof IMG as IMG'.
  unfold asan_img_ok in IMG'.
  pose proof (art_lo asegs R HIA) as ALO.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (hcs_stack asegs R HIA h) as SCS0.
  pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn [Z.pow Z.of_N Pos.pow] in SPR.
  assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia).
  assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia]).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HALG) as ALGB.
  pose proof (rw_cells_bound _ _ _ _ HPAR) as PARB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, ALGB, PARB.
  pose proof (proj1 HBUF) as BUF0.
  pose proof (munch_refl [(PP, PP + 8); (ALG, ALG + 24); (PAR, PAR + 24); (lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  lx_pre. lxr_pose. lxa_auto [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_getalgA 4 5 6] [PP; ALG; PAR].
  lx_pre. lx_run_tac (PLANS [] [(0xac120, DSplit)] 52%N [SUM_getlenA; SUM_gettagA; SUM_getboolA; SUM_getintA; SUM_bitstrnullA; SUM_getalgA 4 5 6]).
  lx_tree. all: lxa_unglob.
  all: lazymatch goal with |- context [MS _ _ (ret_pc _) _ _ _ (seg_rom _)] => lxr_leaf; try lx_rejoin; lx_leaf | |- _ => idtac end.
  all: match goal with |- ?g => idtac "lx END FORM A_x509_get_alg_walk: unexpected leaf left:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma A_x509_get_alg_spec : ltac2:(CDefT.buildp (gd_tbl_A_x509_get_alg ()) "PR,$35.PHIA,(36.$37.R1.)P,(38.(31.R2.))P,(6.$4.(39.R3.)$3:.)P,Pm,P,(2.&40.)(3.(2.&8.))P,(3;.R5.R1.)(3<.R2.)P,(17.=(2:.R5.))(3=.$37.R6.R5.$3>.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG MSI RTC NEED0. apply A_x509_get_alg_walk; [exact IMG | | exact NEED0].
  apply A_asn1_get_alg_spec; assumption.
Qed.
