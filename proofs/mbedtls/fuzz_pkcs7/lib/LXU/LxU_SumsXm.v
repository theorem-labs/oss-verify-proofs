(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Arr MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_montmul.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Export LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxTac LxDex.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Export LxU_SumsArr.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac lxp_pows :=
  try change (2 ^ Z.of_N 1)%Z with 2%Z in *; try change (2 ^ Z.of_N 2)%Z with 4%Z in *;
  try change (2 ^ Z.of_N 3)%Z with 8%Z in *; try change (2 ^ Z.of_N 4)%Z with 16%Z in *.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_LxP_SumsXm () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_montmul.MPI_CORE_MONTMUL_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "lxp_montmul_win_post"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_core_montmul.U_MPI_CORE_MONTMUL"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsArr.q"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "Stdlib.ZArith.BinInt.Z.opp"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "Corelib.Numbers.BinNums.positive"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MArr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.LBase"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.Some"; "montmulG_pre"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "montmulG_clob"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.summary"; "RocqVerifyHarness.AgentSubmission.LXU.LxU_SumsArr.SUM_memsetWP"; "SUM_montmulGP"; "SUM_memcpyGP"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lxp_montmul_win_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (TB i an T : Z) (tws ts : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Ltws',(4.(2.&40.))(1.(4.(2.&40.))Lts',(4.(2.&40.))(5.(6.$0.R13.(7.(8.O1:.O19.O18.O17.R12.R11.R10.O16.O15.R?.R>.R=.R<.R;.R:.R9.R8.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R7.R6.R5.R4.)O:.(9.O1:.)O9.(:.(2.&40.))R3.(;.O1;.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.(11.O8.(12.+4.O7.))(11.(11.O8.(12.+4.O7.))(12.+4.O6.)))(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.(12.+4.(11.(12.+2.O6.)+1.))))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O19.)$15.)(14.&40.O19.))(16.(>.$?.$?.)))))O1.R3.)(5.(17.O1;.O1.R3.)(5.(18.O1;.R3.)(5.(19.O1;.R3.O8.R2.)(5.(6.$1:.(1;.(2.&40.)R2.)(1;.(2.&40.)O4.))(5.(19.O1;.R3.O5.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(1<.O1;.R3.O2.(14.&40.O19.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L16748541572.16 L24080940117.80 L24087117522.11 L25368402940.80 L27091799610.118L31555749531.80 L41492896494.11 L41503332457.80 L48057373719.80 L48059422352.11 L49711493966.118L49726617687.89 L52854928993.80 L60868181170.80 L9486395047.86  00000_00`01A02?03T04Z05:05;05<05\06i07g0940:=0;CS2sp2TB1i2an1T2lo3tws2ts2Hi3Han3LTB2LT2D12LO2S1FS2sp2TB1i2an2lo3tws2Hi3Han3LTB2S1S2ra2sp2TB1i1A1B1N1T3tws2ys2zs2ns2ts2Hi3NZ13NZ23NZ33NZ43NZ52LPS2ra2sp2TB1i1A1B1N2an1T3tws2ys2zs2ns2ts3Han3LTB3NZ13NZ23NZ33NZ43NZ52LP3xs'3ts'2LD3LT'S2ra2sp2TB1i1A1B1N1T3tws2ys2zs2ns2ts2Hi3AL13NZ13NZ23NZ33NZ43NZ53TBB2LPS2TB1i2an1T3tws2ts2Hi3Han3LTB2D1FFS2TB1i1N2an3tws2ns2Hi3Han3LTB2D5S2ra2sp2TB1i1A1B1N1T3tws2ys2zs2ns2ts2Hi3NZ13NZ23NZ33NZ43NZ52LP3xs'3ts'2LD3LT'S2ra2sp2TB1i1A1B1N1T3tws2ys2zs2ns2ts2Hi3NZ13NZ23NZ33NZ43NZ52LPS2ra2sp2TB1i1A1B1N2an1T3tws2ys2zs2ns2ts3Han3LTB3NZ13NZ23NZ33NZ43NZ52B13TBB2LPS2ra2sp2TB1i1A1B1N2an1T3tws2ys2zs2ns2ts2Hi3Han3LTB3NZ13NZ23NZ33NZ43NZ52LPS2ra2sp2TB1i1A1B1N2an1T3tws2ys2zs2ns2ts2Hi3Han3LTB3NZ13NZ23NZ33NZ43NZ5". (* [comment removed for export] *)
Lemma lxp_montmul_win : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PTB,$?.Pi,$?.PA,$?.PB,$?.Pbn,$?.PN,$?.Pan,$?.PT,$?.Plo,$?.Ptws,(4.(2.&40.))Pys,(4.(2.&40.))Pzs,(4.(2.&40.))Pns,(4.(2.&40.))Pts,(4.(2.&40.))P,(19.$1>.R?.R>.R5.)P,(1?.$1>.R10.R=.(20.R5.))P,(1?.$1>.R11.R=.(20.R5.))P,(1?.$1>.R12.R<.(20.R5.))P,(19.$1>.R13.R;.R5.)P,(21.=R12.)P,(5.(21.+1.R>.)(21.R>.+1387.))P,(5.(21.+1.R11.)(21.R11.+2710.))P,(21.(11.R15.R10.)(22.(1;.(2.&40.)R=.)))P,(21.R11.(22.(1;.(2.&40.)R=.)))P,(21.R14.(22.(1;.(2.&40.)R=.)))P,(21.R13.(22.(1;.(2.&40.)R=.)))P,(21.(11.(12.+2.R14.)+1.)(22.(1;.(2.&40.)R=.)))P,(23.(21.(11.R1;.(12.+4.(22.(1;.(2.&40.)R12.))))R14.)(21.(11.R14.(12.+4.(22.(1;.(2.&40.)R>.))))R1;.))P,(23.(21.(11.R1:.(12.+4.(22.(1;.(2.&40.)R12.))))R15.)(21.(11.R15.(12.+4.(22.(1;.(2.&40.)R?.))))R1:.))P,(23.(21.(11.R1:.(12.+4.(22.(1;.(2.&40.)R12.))))R16.)(21.(11.R16.(12.+4.(22.(1;.(2.&40.)R10.))))R1:.))P,(23.(21.(11.R19.(12.+4.(22.(1;.(2.&40.)R12.))))R17.)(21.(11.R17.(12.+4.(22.(1;.(2.&40.)R11.))))R19.))P,(23.(21.(11.R1:.(12.+4.(22.(1;.(2.&40.)R13.))))R1?.)(21.(11.R1?.(12.+4.(22.(1;.(2.&40.)R16.))))R1:.))P,(6.$?.(24.R20.+4.)=)P,(6.$?.(24.R1?.+4.)=)P,(6.$?.(24.R1?.+4.)=)P,(6.$?.(24.R1>.+4.)=)P,(6.$?.(24.R1=.+4.)=)P,(25.=R25.)P,(25.=R24.)P,(25.=R24.)P,(25.=R23.)P,(25.=R22.)P,(25.(11.R2:.(12.+4.(22.(1;.(2.&40.)R21.))))(26.+2.+40.))P,(25.(11.R29.(12.+4.(22.(1;.(2.&40.)R21.))))(26.+2.+40.))P,(25.(11.R29.(12.+4.(22.(1;.(2.&40.)R21.))))(26.+2.+40.))P,(25.(11.R28.(12.+4.(22.(1;.(2.&40.)R21.))))(26.+2.+40.))P,(25.(11.R27.(12.+4.(22.(1;.(2.&40.)R21.))))(26.+2.+40.))P,(1<.$1>.R30.R27.(14.&40.R50.))P,(21.R28.(13.(14.&40.R51.)$15.))P,(6.$?.(24.(14.&40.R52.)+10.)=)P,(23.(21.(11.R32.(12.+4.(22.(1;.(2.&40.)R29.))))R2:.)(21.(14.&40.R53.)R32.))P,(23.(21.(11.R31.(12.+4.(22.(1;.(2.&40.)R29.))))R2;.)(21.(14.&40.R54.)R31.))P,(23.(21.(11.R31.(12.+4.(22.(1;.(2.&40.)R29.))))R2<.)(21.(14.&40.R55.)R31.))P,(23.(21.(11.R30.(12.+4.(22.(1;.(2.&40.)R29.))))R2=.)(21.(14.&40.R56.)R30.))P,(23.(21.(11.R2?.(12.+4.(22.(1;.(2.&40.)R29.))))R2>.)(21.(14.&40.R57.)R2?.))P,(18.$1>.R38.)P,(6.$?.(24.(14.&40.R5:.)+2.)=)P,(6.(2.&40.)R52.(27.&40.(11.R39.(12.+4.R38.))))P,(6.(2.&40.)R52.(27.&40.R38.))P,(6.(2.&40.)R52.(27.&40.R38.))P,(6.(2.&40.)R52.(27.&40.R38.))P,(6.(2.&40.)R52.(27.&40.R38.))P,(6.(2.&40.)R52.(27.&40.R38.))P,(6.(2.&40.)R51.(27.&40.R38.))(28.$1>.(29.$1>.R62.R61.R60.R5?.R5;.R5:.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R43.R42.R40.R3?.R3:.R39.R37.R33.R38.R41.)(7.(8.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.)R43.(27.&40.$2:.)R42.(:.(2.&40.))R41.(;.$1>.)))")
(* [comment removed for export] *).
Proof.
  unfold MPI_CORE_MONTMUL_STACK. intros until ts.
  intros HTB HA HB HN HT Hi Han Hbn LTB LA LB LN LT D1 D2 D3 D4 D5 AL1 AL2 AL3 AL4 AL5 NZ1 NZ2 NZ3 NZ4 NZ5 B1 B2 B3 B4 B5 ST LO SPA S1 S2 S3 S4 S5 MI RA -> -> -> -> -> -> ->.
  pose proof (u32arr_bound _ _ _ _ HTB) as TBB.
  pose proof (firstn_skipn (Z.to_nat i) tws) as EY. symmetry in EY.
  assert (LP : length (firstn (Z.to_nat i) tws) = Z.to_nat i) by (rewrite firstn_length; lia).
  pose proof HTB as HTB0. rewrite EY in HTB. apply u32arr_app in HTB. destruct HTB as [Hlo Hhi]. rewrite LP in Hhi.
  replace (TB + 4 * Z.of_nat (Z.to_nat i)) with (TB + 4 * i) in Hhi by lia.
  pose proof U_mpi_core_montmul_spec as SPEC. unfold mpi_core_montmul_stmt, MPI_CORE_MONTMUL_STACK in SPEC.
  eapply evt_mono.
  { eapply (SPEC ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ _ _ a6 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (TB + 4 * i) A B bn N an T lo (skipn (Z.to_nat i) tws) ys zs ns ts);
        try reflexivity; try eassumption; try (clear D1 D2 D3 D4 D5 S1 S2 S3 S4 S5; rewrite ?skipn_length; lia).
    all: rewrite skipn_length.
    { clear - D1 Hi Han LTB TBB. lia. } { clear - D5 Hi Han LTB TBB. lia. } { clear - S1 Hi Han LTB TBB. lia. } }
  intros ms' PO. unfold mpi_core_montmul_post in PO. unfold lxp_montmul_win_post.
  destruct PO as (xt0 & xt1 & xt2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & m' & xs' & ts' & -> & MU & WM & MI' & HD & LD & SK & HT' & LT' & SKT & ST').
  do 16 eexists. exists (firstn (Z.to_nat i) tws ++ xs'), ts'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  split. { apply u32arr_app. split. { eapply u32arr_transport; [exact Hlo | exact MU | exact WM |]. cbn [disjoint_from]. rewrite LP. unfold MPI_CORE_MONTMUL_STACK in *. clear - D1 S1 LT LTB Hi Han LO TBB. lia. }
           rewrite LP. replace (TB + 4 * Z.of_nat (Z.to_nat i)) with (TB + 4 * i) by lia. exact HD. }
  split. { rewrite app_length, LD, LP, skipn_length. lia. }
  split; [exact HT'|]. split; [exact LT'|]. exact ST'.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L11805649803.80L19054383986.62L3069391972.50 L32607120735.60L32607459445.80L32992720649.80L35323277533.50L40614287107.80L42513551668.62L4778019672.80 L60546950992.55L64303274215.63L64303323238.62L66125982750.62L66125999263.63L68150233355.63L68150282634.6200000P01901H01h02H03103?03_04A04l05B05f06J07307\08I096S1X2ws2ss1i1k1A2Bm1C2Hi2LA2LB2LCS2ws2ss1i1k1A2Bm1C2Hi2Hk3Hik3Hks2LA2LB2LCS2ws2ss1i1k3HikS1X2ws2ss1i1k1A2Bm1C2Hi2LA2LB2LCS1X2ws2ss1i1k1A2Bm1C2Hi2LA2LB2LCS2ws2ss1i1k1A2Bm1C2Hi2Hk3Hik3Hks2LA2LB2LCS2ws2ss1i1k2HkS1X2ws2ss1i1k1A2Bm1C2Hi2LA2LB2LCS1X1S2ws2ss1i1k1A2Bm1C2AP2LA2LB2LCS1X2ws2ss1i1k1A2Bm1C2Hi2Hk3Hik3Hks2LA2LB2LCS2ws2ss1i1k1A2Bm2LA2LBS1S2ws2ss1i1k1A2Bm1C3ST42SB2LA2LB2LCS1S2ws2ss1i1k1A2Bm1C3ST42SB2LA2LB2LCS1X2ws2ss1i1k1A2Bm1C2XP2Hi2XT2UB2LA2LB2LCS1X2ws2ss1i1k1A2Bm1C2XP2Hi2XT2UB2LA2LB2LCS1X2ws2ss1i1k1A2Bm1C2XP2Hi2Hk3Hik2UB2LA2LB2LCS1X2ws2ss1i1k1A2Bm1C2XP2Hi2Hk3Hik2UB2LA2LB2LC". (* [comment removed for export] *)
Lemma lxp_memcpy_limbs : ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.PS,$?.Pws,(4.(2.&40.))Pss,(4.(2.&40.))Pi,$?.Pk,$?.P,(19.$1>.R7.R6.R4.)P,(1?.$1>.R8.R6.(20.R4.))P,(25.=R8.)P,(21.=R5.)P,(21.=R5.)P,(21.(11.R7.R6.)(22.(1;.(2.&40.)R9.)))P,(21.R7.(22.(1;.(2.&40.)R9.)))P,(25.(11.R=.(12.+4.R9.))(26.+2.+40.))P,(25.R=.(26.+2.+40.))P,(23.(21.(11.R>.(12.+4.R:.))(11.R?.(12.+4.R;.)))(21.(11.(11.R?.(12.+4.R;.))(12.+4.R:.))R>.))P,(18.$1>.R11.)P,(6.(2.&40.)R2:.(27.&40.(11.R11.(12.+4.R=.))))P,(6.(2.&40.)R2:.(27.&40.R11.))P,(6.(2.&40.)R2:.(27.&40.(12.+4.R>.)))(28.$1>.Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3',(2.&40.)(1.(2.&40.)La4',(2.&40.)(1.(2.&40.)La5',(2.&40.)(1.(2.&40.)La6',(2.&40.)(1.(2.&40.)La7',(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lws',(4.(2.&40.))(5.(6.$0.R11.(7.(8.R47.R46.R45.R44.R10.R?.R>.R40.R3?.R3>.R=.R<.R;.R:.R9.R8.R7.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R6.R5.R4.R3.)R28.(9.R47.)R27.(:.(2.&40.))R2.(;.$1>.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.(11.R25.(12.+4.R21.))(11.(11.R25.(12.+4.R21.))(12.+4.R20.)))(16.(>.$?.$?.)))R26.R2.)(5.(17.$1>.R26.R2.)(5.(18.$1>.R2.)(5.(19.$1>.R2.R25.R1.)(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)R23.)))))))))))))))))))))))(7.(8.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(27.&40.+46:40.)R16.(:.(2.&40.))R15.(;.$1>.)))")
(* [comment removed for export] *).
Proof.
  intros until k. intros U HS XP Hi Hk Hik Hks XT ST4 AP MI -> -> ->.
  pose proof (u32arr_bound _ _ _ _ U) as UB. pose proof (u32ro_bound _ _ _ _ HS) as SB.
  destruct (split3 ws (Z.to_nat i) (Z.to_nat (i + k)) ltac:(lia) ltac:(lia)) as (EY & LA & LB).
  set (A := firstn (Z.to_nat i) ws) in *. set (Bm := firstn _ (skipn _ ws)) in *. set (C := skipn (Z.to_nat (i + k)) ws) in *.
  assert (LC : length C = (length ws - Z.to_nat (i + k))%nat) by (subst C; rewrite skipn_length; lia).
  pose proof U as U0. rewrite EY in U. apply u32arr_app in U. destruct U as [UA U]. apply u32arr_app in U. destruct U as [UBm UC].
  rewrite LA in UBm, UC. rewrite LB in UC. apply u32arr_cells in UBm. rewrite LB in UBm.
  replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) in UBm, UC by lia.
  pose proof HS as HS1. rewrite <- (firstn_skipn (Z.to_nat k) ss), u32s_app in HS1. apply bytes_at_app in HS1. destruct HS1 as [HS1 _].
  pose proof U_memcpy_spec as SP. unfold memcpy_stmt in SP.
  eapply evt_mono.
  { eapply SP with (src := u32s (firstn (Z.to_nat k) ss)); rewrite ?unsigned_lit by lia.
    - exact HS1.
    - rewrite u32s_length, firstn_length. lia.
    - replace (Z.to_nat (4 * k)) with (4 * (Z.to_nat (i + k) - Z.to_nat i))%nat by lia. exact UBm.
    - lia.
    - exact MI. }
  clear SP. intros ms' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & HZ & _).
  apply (u32arr_of_cells usegs m' _ _ _ (firstn (Z.to_nat k) ss)) in HZ; [| reflexivity ].
  do 15 eexists. exists (A ++ (firstn (Z.to_nat k) ss ++ C)).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split.
  - apply u32arr_app. split.
    + eapply u32arr_transport; [exact UA| exact MU| exact WM| cbn; rewrite LA; lia].
    + rewrite LA. apply u32arr_app. split.
      * replace (X + 4 * Z.of_nat (Z.to_nat i)) with (X + 4 * i) by lia. exact HZ.
      * rewrite firstn_length. replace (X + 4 * Z.of_nat (Z.to_nat i) + 4 * Z.of_nat (Nat.min (Z.to_nat k) (length ss))) with (X + 4 * i + 4 * Z.of_nat (Z.to_nat (i + k) - Z.to_nat i)) by lia.
        eapply u32arr_transport; [exact UC| exact MU| exact WM| cbn; rewrite LC; lia].
  - rewrite !app_length, firstn_length, LA, LC. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition montmulG_pre : list pfact := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "(=.$2;.(2<.(2=.^9.)(2=.^3.))(=.$2;.(2<.(2=.^;.)(2=.^4.))(=.$2;.(2>.(2?.+1.)(2=.^:.))(=.$2;.(2>.(2=.^:.)(2?.+1387.))(=.$2;.(2>.(2?.+1.)(2=.^8.))(=.$2;.(2>.(2=.^8.)(2?.+2710.))(=.$2;.(2>.(2=.^1.)(2=.^5.))(=.$2;.(30.(31.(2=.^5.)(32.-1.(2=.^1.)))&2.)(=.$2;.(2>.(31.(2=.^5.)(32.+4.(2=.^:.)))(31.(2=.^1.)(32.+4.(2=.^<.))))(=.$2;.(2>.(2=.^1.)(2=.^6.))(=.$2;.(30.(31.(2=.^6.)(32.-1.(2=.^1.)))&2.)(=.$2;.(2>.(31.(2=.^6.)(32.+4.(2=.^:.)))(31.(2=.^1.)(32.+4.(2=.^<.))))(=.$2;.(2>.(2=.^2.)(2=.^7.))(=.$2;.(30.(31.(2=.^7.)(32.-1.(2=.^2.)))&2.)(=.$2;.(2>.(31.(2=.^7.)(32.+4.(2=.^8.)))(31.(2=.^2.)(32.+4.(2=.^=.))))(=.$2;.(2>.(2=.^:.)(2=.^>.))(=.$2;.(2>.(31.(32.+2.(2=.^:.))(2?.+1.))(2=.^?.))(=.$2;.(33.(2=.^1.)(32.+4.(2=.^<.))(2=.^4.)(32.+4.(2=.^?.)))(=.$2;.(33.(2=.^2.)(32.+4.(2=.^=.))(2=.^4.)(32.+4.(2=.^?.)))(=.$2;.(33.(2=.^3.)(32.+4.(2=.^>.))(2=.^4.)(32.+4.(2=.^?.)))(=.$2;.(33.(2=.^3.)(32.+4.(2=.^>.))(2=.^1.)(32.+4.(2=.^<.)))(=.$2;.(30.(34.^1.)&2.)(=.$2;.(30.(34.^2.)&2.)(=.$2;.(30.(34.^3.)&2.)(=.$2;.(30.(34.^4.)&2.)(=.$2;.(35.(2?.=)(2=.^1.))(=.$2;.(35.(2?.=)(2=.^2.))(=.$2;.(35.(2?.=)(2=.^3.))(=.$2;.(35.(2?.=)(2=.^4.))(=.$2;.(35.(31.(2=.^1.)(32.+4.(2=.^<.)))(2?.(26.+2.+40.)))(=.$2;.(35.(31.(2=.^2.)(32.+4.(2=.^=.)))(2?.(26.+2.+40.)))(=.$2;.(35.(31.(2=.^3.)(32.+4.(2=.^>.)))(2?.(26.+2.+40.)))(=.$2;.(35.(31.(2=.^4.)(32.+4.(2=.^?.)))(2?.(26.+2.+40.)))(=.$2;.(2>.(2=.^11.)(31.(2=.^10.)(2?.(36.$15.))))(=.$2;.(30.(34.^10.)&4.)(=.$2;.(37.(31.(2=.^1.)(32.+4.(2=.^<.)))(2=.^11.)(2=.^10.)(2=.^1.))(=.$2;.(37.(31.(2=.^2.)(32.+4.(2=.^=.)))(2=.^11.)(2=.^10.)(2=.^2.))(=.$2;.(37.(31.(2=.^3.)(32.+4.(2=.^>.)))(2=.^11.)(2=.^10.)(2=.^3.))(=.$2;.(37.(31.(2=.^4.)(32.+4.(2=.^?.)))(2=.^11.)(2=.^10.)(2=.^4.))(=.$2;.(30.(34.^12.)&1.)(=.$2;.(2>.(2?.=)(2=.^10.))(=.$2;.(2>.(2=.^10.)(2?.(13.$38.+1.)))(=.$2;.(2>.(2?.=)(2=.^12.))(=.$2;.(2>.(2=.^12.)(2?.(13.$38.+1.)))(16.$2;.)))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).
Definition montmulG_clob : list (Z * positive) := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "(=.(>.$?.$39.)(10.$?.$39.+5.^13.)(=.(>.$?.$39.)(10.$?.$39.+6.^14.)(=.(>.$?.$39.)(10.$?.$39.+7.^15.)(=.(>.$?.$39.)(10.$?.$39.+:.^16.)(=.(>.$?.$39.)(10.$?.$39.+;.^17.)(=.(>.$?.$39.)(10.$?.$39.+<.^18.)(=.(>.$?.$39.)(10.$?.$39.+=.^19.)(=.(>.$?.$39.)(10.$?.$39.+>.^1:.)(=.(>.$?.$39.)(10.$?.$39.+?.^1;.)(=.(>.$?.$39.)(10.$?.$39.+10.^1<.)(=.(>.$?.$39.)(10.$?.$39.+11.^1=.)(=.(>.$?.$39.)(10.$?.$39.+1<.^1>.)(=.(>.$?.$39.)(10.$?.$39.+1=.^1?.)(=.(>.$?.$39.)(10.$?.$39.+1>.^20.)(=.(>.$?.$39.)(10.$?.$39.+1?.^21.)(16.(>.$?.$39.)))))))))))))))))")
(* [comment removed for export] *).
Definition SUM_montmulGP (k kB kN kT : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "(3:.$2:.$3;.#12.#?.#0.(=.(>.$?.$39.)(10.$?.$39.+:.^5.)(=.(>.$?.$39.)(10.$?.$39.+;.^6.)(=.(>.$?.$39.)(10.$?.$39.+<.^7.)(=.(>.$?.$39.)(10.$?.$39.+=.^8.)(=.(>.$?.$39.)(10.$?.$39.+>.^9.)(=.(>.$?.$39.)(10.$?.$39.+?.^:.)(=.(>.$?.$39.)(10.$?.$39.+11.^;.)(=.(>.$?.$39.)(10.$?.$39.+2.^10.)(=.(>.$?.$39.)(10.$?.$39.+1.^12.)(16.(>.$?.$39.)))))))))))(=.(>.$39.$1:.)(10.$39.$1:.^1.O4.)(=.(>.$39.$1:.)(10.$39.$1:.^2.O3.)(=.(>.$39.$1:.)(10.$39.$1:.^3.O2.)(=.(>.$39.$1:.)(10.$39.$1:.^4.O1.)(16.(>.$39.$1:.))))))(:.$39.)(=.$3<.(3=.(2=.^1.)&4.(3>.^1.)(2=.^<.)$3?.)(=.$3<.(3=.(2=.^2.)&4.(3>.^2.)(2=.^=.)$3;.)(=.$3<.(3=.(2=.^3.)&4.(3>.^3.)(2=.^>.)$3;.)(=.$3<.(3=.(2=.^4.)&4.(3>.^4.)(2=.^?.)$3?.)(16.$3<.)))))(40.(>.$39.$39.)(10.$39.$39.^11.^10.))(16.(>.(>.$39.$39.)$39.))(16.$3<.)$41.(=.(>.$42.$42.)(10.$42.$42.(2=.^5.)(31.(2=.^5.)(32.+4.(2=.^:.))))(=.(>.$42.$42.)(10.$42.$42.(2=.^4.)(31.(2=.^4.)(32.+4.(31.(32.+2.(2=.^:.))(2?.+1.)))))(=.(>.$42.$42.)(10.$42.$42.(31.(2=.^10.)(2?.(36.$15.)))(2=.^10.))(16.(>.$42.$42.)))))$43.(=.$3<.(3=.(2=.^1.)&4.(3>.^5.)(2=.^<.)$3?.)(=.$3<.(3=.(2=.^4.)&4.(3>.^6.)(2=.^?.)$3?.)(=.$3<.(44.(2=.^11.)(2=.^10.))(16.$3<.))))(16.$2;.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@L10351939025.141L10384330990.166L12423920700.141L13040405718.141L14364034141.136L15026208665.141L15372568033.141L2054897152.166 L23872988551.141L23998152115.141L2481198071.141 L25367664761.141L29189243630.141L29589294294.141L30319199963.141L33309804251.141L34500388447.141L39349998163.134L40233199518.141L46189906732.141L47582620807.141L47965399564.141L50288272991.141L52448825512.139L60880762663.141L61347853952.141L64248983836.141L64965053867.141L66111239975.141L66517337139.141L68259315013.141L7957986244.138 L8484802731.132 L8702331721.141 00001Z03Y05K08e0:J0<10=f0?g0BQ0E?0FP0HB0KX0O20Q20Rf0UT0W10Y10Z]0[n0]U0`X0bS0dN0gh0k>0ml0og11S13H15G16b18[S2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts1i3PR53PR84PR114PR244PR254PR264PR274PR394PR412Ep2iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2NT3SPu2RA3tws3bbs2ns2ts1i2LT3PR53PR84PR114PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpB4tws'3ts'4LTB'3LT'S2TB2BB3NBs2TT2pX2pA2pB2NN3SPu2RA3tws3bbs2ns2ts1i2LN3PR53PR84PR114PR244PR254PR264PR274PR304PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn2an3NTB3NBB2NN2NT3SPu2LO2RA3tws3bbs2ns2ts1i3LTB2LN2LT3PR13PR33PR53PR73PR84PR104PR114PR134PR144PR154PR164PR174PR184PR194PR204PR244PR254PR264PR274PR334PR344PR354PR364PR374PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts3PR53PR84PR114PR124PR244PR254PR264PR274PR394PR411i2iA3EpAS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts1i3PR53PR84PR114PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an2NN3SPu2RA3tws3bbs2ns2ts1i2LN3PR53PR84PR114PR144PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3NTB3SPu2RA3tws3bbs2ns2ts1i3LTB3PR53PR84PR114PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpB4tws'3ts'4LTB'3LT'S2TB2BB3NBs2TT2pX2pA2pB2an3NTB2NN2NT3SPu2RA3tws3bbs2ns2ts1i2LN2LT3PR13PR53PR73PR84PR104PR114PR144PR154PR164PR184PR194PR224PR234PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an3NTB2NN2NT3SPu2RA3tws3bbs2ns2ts1i3LTB2LN2LT3PR13PR53PR73PR84PR104PR114PR144PR154PR164PR184PR194PR204PR234PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an3SPu2RA3tws3bbs2ns2ts1i3PR13PR24PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2NT3SPu2RA3tws3bbs2ns2ts1i2LT3PR53PR84PR114PR244PR254PR264PR274PR314PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn2an3NTB3NBB2NN2NT3SPu2LO2RA3tws3bbs2ns2ts1i2LN2LT3PR13PR33PR53PR73PR84PR104PR114PR134PR144PR154PR164PR174PR184PR194PR234PR244PR254PR264PR274PR334PR344PR354PR364PR374PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn2an3NTB3NBB2NN2NT3SPu2LO2RA3tws3bbs2ns2ts1i3LBB2LN2LT3PR13PR33PR53PR73PR84PR104PR114PR134PR144PR154PR164PR174PR184PR194PR214PR244PR254PR264PR274PR334PR344PR354PR364PR374PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn3NBB3SPu2RA3tws3bbs2ns2ts1i3LBB3PR33PR53PR84PR114PR134PR244PR254PR264PR274PR294PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3NTB3SPu2RA3tws3bbs2ns2ts1i3LTB3PR53PR84PR114PR244PR254PR264PR274PR284PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an3NTB2NN2NT3SPu2RA3tws3bbs2ns2ts1i3LTB2LN2LT3PR13PR53PR73PR84PR104PR114PR144PR154PR164PR184PR194PR204PR234PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts3PR53PR83PR94PR114PR244PR254PR264PR274PR394PR411iS2TB2BB3NBs2TT2pX2pA2pB2an3NTB3SPu2RA3tws3bbs2ns2ts1i3LTB3PR13PR53PR84PR104PR114PR244PR254PR264PR274PR284PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts1i3PR53PR84PR114PR204PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn3SPu2RA3tws3bbs2ns2ts1i3PR33PR44PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts1i3PR53PR84PR114PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn2an3NTB3NBB2NN2NT3SPu2RA3tws3bbs2ns2ts1i3LBB2LN2LT3PR13PR33PR53PR73PR84PR104PR114PR134PR144PR154PR164PR174PR184PR194PR214PR234PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn3NBB3SPu2RA3tws3bbs2ns2ts3LBB3PR33PR53PR84PR114PR134PR244PR254PR264PR274PR394PR411i2iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an3NTB3SPu2RA3tws3bbs2ns2ts1i3LTB3PR13PR53PR84PR104PR114PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn2an3NTB3NBB2NN2NT3SPu2LO2RA3tws3bbs2ns2ts1i3LTB2LN2LT3PR13PR33PR53PR73PR84PR104PR114PR134PR144PR154PR164PR174PR184PR194PR204PR244PR254PR264PR274PR334PR344PR354PR364PR374PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn2an3NTB3NBB2NN2NT3SPu2LO2RA3tws3bbs2ns2ts1i2LN2LT3PR13PR33PR53PR73PR84PR104PR114PR134PR144PR154PR164PR174PR184PR194PR224PR244PR254PR264PR274PR334PR344PR354PR364PR374PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an3NTB2NN2NT3SPu2RA3tws3bbs2ns2ts1i3LTB2LN2LT3PR13PR53PR73PR84PR104PR114PR144PR154PR164PR184PR194PR204PR224PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2bn3NBB3SPu2RA3tws3bbs2ns2ts1i3LBB3PR33PR53PR84PR114PR134PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts1i3PR53PR84PR114PR214PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an2NT3SPu2RA3tws3bbs2ns2ts1i2LT3PR53PR84PR114PR154PR244PR254PR264PR274PR394PR412iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB2an3NTB3SPu2RA3tws3bbs2ns2ts3LTB3PR13PR53PR73PR84PR104PR114PR244PR254PR264PR274PR394PR411i2iA3EpA2iB3EpBS2TB2BB3NBs2TT2pX2pA2pB3SPu2RA3tws3bbs2ns2ts3PR53PR63PR84PR114PR244PR254PR264PR274PR394PR41S2TB2BB3NBs2TT2pX2pA2pB2an3NTB3SPu2RA3tws3bbs2ns2ts1i3LTB3PR53PR73PR84PR114PR244PR254PR264PR274PR394PR412Ep2iA3EpA2iB3EpB". (* [comment removed for export] *)
Lemma sum_montmulGP_valid : forall AL GS k kB kN kT, summary_validG usegs AL GS (SUM_montmulGP k kB kN kT).
Proof.
  intros AL GS k kB kN kT. unfold SUM_montmulGP, montmulG_pre, montmulG_clob, q, MPI_CORE_MONTMUL_STACK. lx_sum_unfold.
  intros TB BB NBs TT pX pA pB bn pN an pT NTB NBB NN NT SPu LO RA tws bbs ns ts CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB1 GB2 GB3 GB4 R10 R11 R12 R13 R14 R15 R17 R2 R1 ST [HTB LTB] [HBB LBB] [HN LN] [HT LT].
  intros EQN EQT PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24 PR25 PR26 PR27 PR28 PR29
         PR30 PR31 PR32 PR33 PR34 PR35 PR36 PR37 PR38 PR39 PR40 PR41 PR42.
  lxp_pows. subst pN pT.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply lxp_uw64; assumption).
  assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply lxp_uw64; assumption).
  set (i := (pX - TB) / 4). assert (Ep : pX = TB + 4 * i) by (subst i; lia).
  set (iA := (pA - TB) / 4). assert (EpA : pA = TB + 4 * Z.of_nat (Z.to_nat iA)) by (subst iA; lia).
  set (iB := (pB - BB) / 4). assert (EpB : pB = BB + 4 * Z.of_nat (Z.to_nat iB)) by (subst iB; lia).
  pose proof (lxp_u32ro_skipn _ _ _ _ (Z.to_nat iA) (u32arr_ro _ _ _ _ HTB) ltac:(lia)) as HA. rewrite <- EpA in HA.
  pose proof (lxp_u32ro_skipn _ _ _ _ (Z.to_nat iB) HBB ltac:(lia)) as HB. rewrite <- EpB in HB.
  rewrite Ep in R10.
  pose proof lxp_montmul_win as SP. unfold MPI_CORE_MONTMUL_STACK in SP.
  eapply evt_cut.
  { eapply (SP x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
               TB i pA pB bn NBs an TT LO tws (skipn (Z.to_nat iA) tws) (skipn (Z.to_nat iB) bbs) ns ts);
      rewrite ?U2, ?U1, ?skipn_length; first [eassumption | lia | idtac]. }
  clear SP. cbv beta. intros ms' POST. unfold lxp_montmul_win_post, MPI_CORE_MONTMUL_STACK in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & tws' & ts' & -> & MU & WM & MI' & HTB' & LTB' & HT' & LT' & ST').
  apply evt_done. rewrite U2 in MU, ST'. rewrite <- Ep in MU.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_memcpyGP (k kS : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "(3:.+46:40.$3;.#7.#>.#0.(=.(>.$?.$39.)(10.$?.$39.+:.^3.)(=.(>.$?.$39.)(10.$?.$39.+;.^4.)(=.(>.$?.$39.)(10.$?.$39.+<.^5.)(16.(>.$?.$39.)))))(=.(>.$39.$1:.)(10.$39.$1:.^1.O2.)(=.(>.$39.$1:.)(10.$39.$1:.^2.O1.)(16.(>.$39.$1:.))))(:.$39.)(=.$3<.(3=.(2=.^1.)&4.(3>.^1.)(2=.^6.)$3?.)(=.$3<.(3=.(2=.^2.)&4.(3>.^2.)(2=.^7.)$3;.)(16.$3<.)))(:.(>.$39.$39.))(16.(>.(>.$39.$39.)$39.))(16.$3<.)(=.$2;.(2<.(2=.^4.)(2=.^2.))(=.$2;.(2>.(2=.^1.)(2=.^3.))(=.$2;.(30.(31.(2=.^3.)(32.-1.(2=.^1.)))&2.)(=.$2;.(30.(2=.^5.)&2.)(=.$2;.(2>.(2?.=)(2=.^5.))(=.$2;.(2>.(31.(2=.^3.)(2=.^5.))(31.(2=.^1.)(32.+4.(2=.^6.))))(=.$2;.(2>.(2=.^5.)(32.+4.(2=.^7.)))(=.$2;.(33.(2=.^2.)(2=.^5.)(2=.^3.)(2=.^5.))(=.$2;.(35.(2?.=)(2=.^1.))(=.$2;.(35.(2=.^3.)(2?.(26.+2.+40.)))(=.$2;.(35.(2=.^2.)(2?.(26.+2.+40.)))(16.$2;.))))))))))))(=.(>.$42.$42.)(10.$42.$42.(2=.^3.)(31.(2=.^3.)(2=.^5.)))(16.(>.$42.$42.)))(=.(>.$?.$39.)(10.$?.$39.+5.^8.)(=.(>.$?.$39.)(10.$?.$39.+6.^9.)(=.(>.$?.$39.)(10.$?.$39.+7.^:.)(=.(>.$?.$39.)(10.$?.$39.+;.^;.)(=.(>.$?.$39.)(10.$?.$39.+<.^<.)(=.(>.$?.$39.)(10.$?.$39.+=.^=.)(=.(>.$?.$39.)(10.$?.$39.+>.^>.)(=.(>.$?.$39.)(10.$?.$39.+?.^?.)(=.(>.$?.$39.)(10.$?.$39.+10.^10.)(=.(>.$?.$39.)(10.$?.$39.+11.^11.)(=.(>.$?.$39.)(10.$?.$39.+1<.^12.)(=.(>.$?.$39.)(10.$?.$39.+1=.^13.)(=.(>.$?.$39.)(10.$?.$39.+1>.^14.)(=.(>.$?.$39.)(10.$?.$39.+1?.^15.)(16.(>.$?.$39.))))))))))))))))(=.$3<.(3=.(2=.^1.)&4.(3>.^3.)(2=.^6.)$3?.)(16.$3<.))(16.$2;.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L10351776431.76L15398204505.97L226240730.97  L32201852983.73L35259269050.76L41836597480.76L4233207393.76 L42513780298.76L45411784922.74L54041914784.76L60153744220.76L62654887716.7600000M01301\02802_03M03j04P04k05E05b06LS1X1p1n2xs2ss1i2kk3PR13PR42EpS1X1p1n2xs2ss1i2kk3PR13PR42En3xs'4LEN'S1X1p1n2NX2xs2ss1i2kk2LX3PR13PR43xs'4LEN'S1X1p1n2xs2ss3PR13PR23PR42kkS1X1p1n2NS2xs2ss1i2kk2LS3PR13PR43PR62EnS1X1p1n2NX2xs2ss1i2kk2LX3PR13PR43PR53PR92XB2EpS1X1p1n2xs2ss1i2kk3PR13PR42EnS1X1S1p1n2xs2ss1i2kk3PR13PR43PR72Ep2EnS1X1p1n2xs2ss3PR13PR33PR41iS1X1p1n2xs2ss1i2kk3PR43PR8S1X1S1p1n2xs2ss1i2kk3PR44PR10S1X1p1n2NX2xs2ss1i2kk2LX3PR13PR43PR52Ep2En". (* [comment removed for export] *)
Lemma sum_memcpyGP_valid : forall AL GS k kS, summary_validG usegs AL GS (SUM_memcpyGP k kS).
Proof.
  intros AL GS k kS. unfold SUM_memcpyGP, q. lx_sum_unfold.
  intros X S p s n NX NS xs ss CS F fc m.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  intros ALLCS _ MI GB1 GB2 R10 R11 R12 _ [HX LX] [HS LS] EQS PR1 PR2 PR3 PR4 PR5 PR6 PR7 PR8 PR9 PR10.
  lxp_pows. subst s.
  apply (evt_evtA_all usegs AL CS _ _ ALLCS).
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  set (i := (p - X) / 4). set (kk := n / 4).
  assert (Ep : p = X + 4 * i) by (subst i; lia). assert (En : n = 4 * kk) by (subst kk; lia).
  rewrite Ep in R10. rewrite En in R12.
  eapply evt_cut.
  { eapply (lxp_memcpy_limbs x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
                                 x24 x25 x26 x27 x28 x29 x30 x31 F fc m X S xs ss i kk);
      first [exact HX | exact HS | exact MI | exact R10 | exact R11 | exact R12 | lia]. }
  cbv beta. intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & xs' & -> & MU & WM & MI' & HX' & LEN').
  apply evt_done. rewrite <- Ep in MU. replace (p + 4 * kk) with (p + n) in MU by lia.
  lx_sum_post.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUMSXM_PRE : list summary := ltac2:(CDefT.buildp (gd_tbl_LxP_SumsXm ()) "(=.$45.(46.#0.)(=.$45.(47.#0.#1.#4.#5.)(=.$45.(48.#0.#6.)(=.$45.(47.#0.#0.#4.#5.)(=.$45.(48.#2.#0.)(16.$45.))))))")
(* [comment removed for export] *).
Definition SUMSXM_SQ : list summary := [SUM_montmulGP 2 2 4 5].
Definition SUMSXM_MUL : list summary := [SUM_montmulGP 2 3 4 5].
Lemma sumsxm_pre_ok : forall GS AL, Forall (summary_okG usegs AL GS) SUMSXM_PRE.
Proof.
  intros GS AL. unfold SUMSXM_PRE. repeat constructor; apply apply_summary_soundG;
    auto using sum_memsetWP_valid, sum_memcpyGP_valid, sum_montmulGP_valid.
Qed.
Lemma sumsxm_sq_ok : forall GS AL, Forall (summary_okG usegs AL GS) SUMSXM_SQ.
Proof. intros GS AL. unfold SUMSXM_SQ. repeat constructor; apply apply_summary_soundG; auto using sum_montmulGP_valid. Qed.
Lemma sumsxm_mul_ok : forall GS AL, Forall (summary_okG usegs AL GS) SUMSXM_MUL.
Proof. intros GS AL. unfold SUMSXM_MUL. repeat constructor; apply apply_summary_soundG; auto using sum_montmulGP_valid. Qed.
