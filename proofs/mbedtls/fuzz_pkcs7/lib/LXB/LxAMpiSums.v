(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_mla.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts A_mpi_core_mla.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface Arr CellsX MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum LxSoundSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_LxAMpiSums () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla.MPI_CORE_MLA_STACK_A"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla.mpi_core_mla_stmtA"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.min"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "lx_mla_window_postA"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMG"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mla.A_MPI_CORE_MLA"; "Corelib.Init.Datatypes.true"; "Corelib.Numbers.BinNums.positive"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.mfact"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MArr"; "q"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.LBase"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MAobj"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EMulC"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MRo"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.ELit"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.cellx"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.XZ"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.pfact"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLe"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FAl"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EZv"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.EAdd"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FSep"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FLt"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FOr2"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FCr"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.two64"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.expr"; "RocqVerifyHarness.AgentSubmission.LX.LxMem.MStk"; "RocqVerifyHarness.AgentSubmission.LX.LxSum.SUMX"; "RocqVerifyHarness.AgentSubmission.LX.LxDec.FEq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LX.LxSoundSum.summary_okO"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "SUM_amemsetWA"].


Definition q (i : positive) : expr := EZv i.
Notation "a .+ b" := (EAdd a b) (at level 50, left associativity).
Notation "a .- b" := (EAdd a (EMulC (-1) b)) (at level 50, left associativity).

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38557627424.3000009S1z2H12H2". (* [comment removed for export] *)
Lemma uw64 : forall z, 0 <= z -> z <= two64 - 1 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H1 H2. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus, two64 in *. cbn in *. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lx_mla_window_postA (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A i dl : Z) (ws : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_LxAMpiSums ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lws',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O19.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.(11.O6.(12.+4.O5.))(11.(11.O6.(12.+4.O5.))(12.+4.O4.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O17.)$15.)(14.&40.O17.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O19.O1.R2.)(5.(18.O19.R2.)(5.(19.O19.R2.O6.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O5.)R1.)(1<.(2.&40.)(1=.O5.)O3.))(5.(6.(4.(2.&40.))(1>.(2.&40.)(1=.(11.O5.O4.))R1.)(1>.(2.&40.)(1=.(11.O5.O4.))O3.))(1?.O19.R2.O2.(14.&40.O17.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "00A0@L18832045976.101L19720045175.76 L22068547979.76 L24466837619.76 L31541875041.101L32990620730.101L33574382520.101L33586966945.75 L44042767527.72 L4447919927.100 L46086150197.101L47039822340.101L47773950335.76 L5648782177.76  L60600723132.76 L63591997955.76 L64560512919.10100000M01101[02i03M04804\05905]07907Y08=09O0:20:O0;d0<OS2ra2sp1A1i1S2ws2ss2LP3ds'2LDS2ra2sp1A1i1S2ws2ss2Hi3ALA3NZA2AB2LPS2ra2sp1A1i2dl1S2ws2ss3Hdl2LX3NZA2AT2AB2LPS2ra2sp1A1i2dl1S2sl2lo2ws2ss3Hdl2LX2LS3DIS3ALA3ALS3NZA3NZS2LO3SPA2SX3SSX2AB2LPS2ra2sp1A1i2dl1S2ws2ss3NZA2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss3Hdl2LX3NZA2LP3ds'2LDS2ra2sp1A1i1S2ws2ss2Hi3NZA2LP3ds'2LDS2ra2sp1A1i1S2ws2ss2Hi3NZA2LPS2ra2sp1A1i2dl1S2ws2ss2Hi3Hdl2LX3NZAS2ra2sp1A1i2dl1S2sl2lo2ws2ss2Hi3Hdl3Hsl2LX2LS3DIS3ALA3ALS3NZA3NZS2LO3SPA2SX3SSX2AB2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss2LP3ds'2LDS2ra2sp1A1i2dl1S2ws2ss3NZA2LP3ds'2LDS2ra2sp1A1i2dl1S2sl2lo2ws2ss2Hi3Hdl3Hsl2LX3DIS3ALA3ALS3NZA3NZS2LO3SPA2SX3SSX2AB2LPS2ra2sp1A1i2dl1S2ws2ss2Hi2LX3NZA2LPS2ra2sp1A1i1S2ws2ss2Hi3NZA2LPS2ra2sp1A1i2dl1S2sl2lo2ws2ss2Hi3Hdl3Hsl2LX2LS3DIS3ALA3ALS3NZA3NZS2LO3SPA2SX3SSX2AB2LPS2ra2sp1A1i2dl1S2ws2ss2Hi3Hdl3NZA2LP3ds'2LD". (* [comment removed for export] *)
Lemma lx_mla_windowA : ltac2:(CDefT.buildp (gd_tbl_LxAMpiSums ()) "Psegs,(4.$20.)PAL,$21.PENTRY,$?.P,(22.R3.R2.R1.)PCS,P,$?.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(23.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$?.Pi,$?.Pdl,$?.PS,$?.Psl,$?.Plo,$?.Pws,(4.(2.&40.))Pss,(4.(2.&40.))P,(19.R2?.R9.R8.R2.)P,(24.R30.R:.R6.(25.R2.))P,(26.=R9.)P,(5.(26.=R9.)(26.R9.+2710.))P,(5.(26.=R8.)(26.R8.+2710.))P,(26.(11.R<.R;.)(27.(1;.(2.&40.)R7.)))P,(26.R:.(27.(1;.(2.&40.)R7.)))P,(28.(26.(11.R<.(12.+4.(27.(1;.(2.&40.)R8.))))R?.)(26.(11.R?.(12.+4.(27.(1;.(2.&40.)R9.))))R<.))P,(6.$?.(29.R10.+4.)=)P,(6.$?.(29.R>.+4.)=)P,(2:.=R12.)P,(28.(6.$?.R?.=)(2:.=R10.))P,(2:.(11.R14.(12.+4.(27.(1;.(2.&40.)R>.))))(2;.+2.+40.))P,(2:.(11.R12.(12.+4.(27.(1;.(2.&40.)R>.))))(2;.+2.+40.))P,(1?.R3=.R17.R11.(14.&40.R37.))P,(26.R12.(13.(14.&40.R38.)$15.))P,(6.$?.(29.(14.&40.R39.)+10.)=)P,(28.(26.(11.R19.(12.+4.(27.(1;.(2.&40.)R13.))))R14.)(26.(14.&40.R3:.)R19.))P,(28.(26.(11.R17.(12.+4.(27.(1;.(2.&40.)R13.))))R15.)(26.(14.&40.R3;.)R17.))P,(18.R42.R1<.)P,(6.$?.(29.(14.&40.R3>.)+2.)=)P,(2<.R43.)P,(2=.R44.R41.)P,(2>.R46.R45.R20.)P,(2?.R47.R46.R43.R21.(11.R20.(12.+4.R1?.))(12.+4.R1>.))P,(2?.R48.R47.R44.R22.R1>.(12.+4.(30.R1?.R1=.)))P,(31.R45.R1=.(13.(14.&40.R43.)R1=.))P,(6.(2.&40.)R3<.(32.&40.(11.R23.(12.+4.R22.))))P,(6.(2.&40.)R3<.(32.&40.R22.))P,(6.(2.&40.)R3<.(32.&40.R22.))P,(6.(2.&40.)R3<.(32.&40.R22.))(33.R4>.R4=.R4:.(34.R4>.R49.R48.R47.R46.R42.R41.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2:.R29.R27.R26.R25.R21.R22.R28.)(7.(8.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.)R2:.(32.&40.R4<.)R29.(:.(2.&40.))R28.(;.R4>.)))")
(* [comment removed for export] *).
Proof.
  intros segs AL ENTRY SPEC. intros until ss. intros HX HS Hi Hdl Hsl LX LS DIS ALA ALS NZA NZS AT ST_ ST LO SPA SX SSX MI RA ALWF CSOK ABS OD OS SCS -> -> -> ->.
  unfold MPI_CORE_MLA_STACK_A in *.
  pose proof (u32arr_bound _ _ _ _ HX) as AB.
  pose proof (firstn_skipn (Z.to_nat i) ws) as EY. symmetry in EY.
  assert (LP : length (firstn (Z.to_nat i) ws) = Z.to_nat i) by (rewrite firstn_length; lia).
  pose proof HX as HX0. rewrite EY in HX. apply u32arr_app in HX. destruct HX as [HXlo HXhi]. rewrite LP in HXhi.
  replace (A + 4 * Z.of_nat (Z.to_nat i)) with (A + 4 * i) in HXhi by lia.
  pose proof SPEC as SP. unfold mpi_core_mla_stmtA, MPI_CORE_MLA_STACK_A in SP.
  eapply evtA_mono.
  { eapply (SP CS ra sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (A + 4 * i) dl S sl lo (skipn (Z.to_nat i) ws) ss);
        try reflexivity; try eassumption; try (rewrite ?skipn_length; lia).
    all: try (rewrite Z.mul_comm, Z.mod_add by lia; exact ALA). }
  intros ms' PO. unfold mpi_core_mla_postA, MPI_CORE_MLA_STACK_A in PO. unfold lx_mla_window_postA, MPI_CORE_MLA_STACK_A.
  destruct PO as (xt0 & xt1 & xt2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & m' & ds' & -> & MU & WM & MI' & HD & LD & SK & ST').
  do 16 eexists. exists (firstn (Z.to_nat i) ws ++ ds'). split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  assert (HXlo' : u32arr segs m' A (firstn (Z.to_nat i) ws)).
  { eapply u32arr_transport; [exact HXlo | exact MU | exact WM |]. cbn [disjoint_from]. rewrite LP. lia. }
  split; [|split; [|split; [|split]]].
  - apply u32arr_app. split; [exact HXlo'|]. rewrite LP. replace (A + 4 * Z.of_nat (Z.to_nat i)) with (A + 4 * i) by lia. exact HD.
  - rewrite app_length, LD, LP, skipn_length. lia.
  - rewrite firstn_app, LP, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by lia. reflexivity.
  - replace (Z.to_nat (i + dl)) with (Z.to_nat i + Z.to_nat dl)%nat by lia.
    rewrite skipn_app, LP. replace (Z.to_nat i + Z.to_nat dl - Z.to_nat i)%nat with (Z.to_nat dl) by lia.
    rewrite skipn_all2 by (rewrite LP; lia). cbn [app]. rewrite SK, skipn_skipn. f_equal. lia.
  - exact ST'.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_mlawA (kA : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAMpiSums ()) "(35.$36.$37.#;.#?.#0.(=.(>.$?.$38.)(10.$?.$38.+:.^1.)(=.(>.$?.$38.)(10.$?.$38.+;.^2.)(=.(>.$?.$38.)(10.$?.$38.+<.^3.)(=.(>.$?.$38.)(10.$?.$38.+=.^4.)(=.(>.$?.$38.)(10.$?.$38.+2.^7.)(=.(>.$?.$38.)(10.$?.$38.+1.^9.)(16.(>.$?.$38.))))))))(=.(>.$38.$1:.)(10.$38.$1:.^5.O1.)(16.(>.$38.$1:.)))(39.$38.^;.)(=.$3:.(3;.(3<.^5.)&4.(3=.^1.)(3<.^6.)$37.)(=.$3:.(3;.(3<.^3.)&4.(3=.^2.)(3<.^:.)$3>.)(16.$3:.)))(39.(>.$38.$38.)(10.$38.$38.^8.^7.))(16.(>.(>.$38.$38.)$38.))(=.$3:.(3?.(3<.^1.)(40.+4.(3<.^2.)))(=.$3:.(3?.(3<.^3.)(40.+4.(3<.^4.)))(=.$3:.(41.(42.+?5>50.)(=.$43.(44.&8.(42.+1099?8.))(16.$43.)))(=.$3:.(41.(42.+1099?8.)(=.$43.(44.&8.(3<.^;.))(16.$43.)))(16.$3:.)))))(=.$45.(46.(42.=)(3<.^2.))(=.$45.(46.(3<.^2.)(42.+2710.))(=.$45.(46.(42.=)(3<.^4.))(=.$45.(46.(3<.^4.)(42.+2710.))(=.$45.(46.(3<.^5.)(3<.^1.))(=.$45.(47.(48.^1.)&2.)(=.$45.(47.(48.^5.)&2.)(=.$45.(47.(48.^3.)&2.)(=.$45.(46.(49.(3<.^1.)(40.+4.(3<.^2.)))(49.(3<.^5.)(40.+4.(3<.^6.))))(=.$45.(46.(3<.^4.)(3<.^:.))(=.$45.(4:.(3<.^3.)(40.+4.(3<.^:.))(3<.^5.)(40.+4.(3<.^6.)))(=.$45.(4;.(42.=)(3<.^5.))(=.$45.(4<.(3<.^4.)(42.=)(42.+1.)(3<.^3.))(=.$45.(4;.(49.(3<.^5.)(40.+4.(3<.^6.)))(42.(2;.+2.+40.)))(=.$45.(4;.(49.(3<.^3.)(40.+4.(3<.^:.)))(42.(2;.+2.+40.)))(=.$45.(46.(3<.^8.)(49.(3<.^7.)(42.-70.)))(=.$45.(47.(48.^7.)&4.)(=.$45.(4<.(49.(3<.^5.)(40.+4.(3<.^6.)))(3<.^8.)(3<.^7.)(3<.^5.))(=.$45.(4<.(49.(3<.^3.)(40.+4.(3<.^:.)))(3<.^8.)(3<.^7.)(3<.^3.))(=.$45.(47.(48.^9.)&1.)(=.$45.(4=.(3<.^8.)(49.(3<.^7.)(40.-1.(3<.^8.))))(=.$45.(46.(42.=)(3<.^7.))(=.$45.(46.(3<.^7.)(42.(13.$4>.+1.)))(=.$45.(46.(42.=)(3<.^9.))(=.$45.(46.(3<.^9.)(42.(13.$4>.+1.)))(16.$45.))))))))))))))))))))))))))(=.(>.$4?.$4?.)(10.$4?.$4?.(3<.^1.)(49.(3<.^1.)(40.+4.(3<.^2.))))(=.(>.$4?.$4?.)(10.$4?.$4?.(49.(3<.^7.)(42.-70.))(3<.^7.))(16.(>.$4?.$4?.))))(=.(>.$?.$38.)(10.$?.$38.+5.^<.)(=.(>.$?.$38.)(10.$?.$38.+6.^=.)(=.(>.$?.$38.)(10.$?.$38.+7.^>.)(=.(>.$?.$38.)(10.$?.$38.+:.^?.)(=.(>.$?.$38.)(10.$?.$38.+;.^10.)(=.(>.$?.$38.)(10.$?.$38.+<.^11.)(=.(>.$?.$38.)(10.$?.$38.+=.^12.)(=.(>.$?.$38.)(10.$?.$38.+>.^13.)(=.(>.$?.$38.)(10.$?.$38.+?.^14.)(=.(>.$?.$38.)(10.$?.$38.+10.^15.)(=.(>.$?.$38.)(10.$?.$38.+11.^16.)(=.(>.$?.$38.)(10.$?.$38.+1<.^17.)(=.(>.$?.$38.)(10.$?.$38.+1=.^18.)(=.(>.$?.$38.)(10.$?.$38.+1>.^19.)(=.(>.$?.$38.)(10.$?.$38.+1?.^1:.)(16.(>.$?.$38.)))))))))))))))))(=.$3:.(3;.(3<.^5.)&4.(3=.^3.)(3<.^6.)$37.)(=.$3:.(50.(3<.^8.)(3<.^7.))(16.$3:.)))(16.$45.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SUM_amemsetWA (kd kn : nat) : summary := ltac2:(CDefT.buildp (gd_tbl_LxAMpiSums ()) "(51.+68258.$37.#;.#?.#0.(=.(>.$?.$38.)(10.$?.$38.+:.^:.)(=.(>.$?.$38.)(10.$?.$38.+;.^2.)(=.(>.$?.$38.)(10.$?.$38.+<.^3.)(=.(>.$?.$38.)(10.$?.$38.+2.^4.)(16.(>.$?.$38.))))))(=.(>.$38.$1:.)(10.$38.$1:.^1.O2.)(=.(>.$38.$1:.)(10.$38.$1:.^6.#1.)(=.(>.$38.$1:.)(10.$38.$1:.^7.#2.)(=.(>.$38.$1:.)(10.$38.$1:.^8.#3.)(=.(>.$38.$1:.)(10.$38.$1:.^;.O1.)(16.(>.$38.$1:.)))))))(:.$38.)(=.$3:.(3;.(3<.^1.)&4.(3=.^1.)(3<.^9.)$37.)(16.$3:.))(39.(>.$38.$38.)(10.$38.$38.^5.^4.))(16.(>.(>.$38.$38.)$38.))(=.$3:.(3?.(3<.^1.)(40.+4.(3<.^9.)))(16.$3:.))(=.$45.(52.(3<.^:.)(3<.^1.))(=.$45.(52.(3<.^9.)(3<.^;.))(=.$45.(52.(3<.^3.)(40.+4.(3<.^9.)))(=.$45.(46.(42.=)(3<.^2.))(=.$45.(4;.(3<.^2.)(42.+100.))(=.$45.(46.(42.=)(3<.^9.))(=.$45.(46.(3<.^9.)(42.+7530.))(=.$45.(46.(3<.^8.)(3<.^5.))(=.$45.(46.(3<.^5.)(49.(3<.^4.)(40.-1.(3<.^7.))))(=.$45.(4=.(3<.^5.)(49.(3<.^4.)(40.-1.(3<.^5.))))(=.$45.(4<.(49.(3<.^1.)(40.+4.(3<.^9.)))(3<.^5.)(3<.^4.)(3<.^1.))(=.$45.(46.(3<.^4.)(3<.^6.))(=.$45.(46.(42.=)(3<.^4.))(=.$45.(46.(3<.^4.)(42.(13.$4>.+1.)))(16.$45.)))))))))))))))(=.(>.$4?.$4?.)(10.$4?.$4?.(3<.^1.)(49.(3<.^1.)(40.+4.(3<.^9.))))(=.(>.$4?.$4?.)(10.$4?.$4?.(3<.^5.)(3<.^4.))(16.(>.$4?.$4?.))))(=.(>.$?.$38.)(10.$?.$38.+:.^<.)(=.(>.$?.$38.)(10.$?.$38.+5.^=.)(=.(>.$?.$38.)(10.$?.$38.+6.^>.)(=.(>.$?.$38.)(10.$?.$38.+7.^?.)(=.(>.$?.$38.)(10.$?.$38.+;.^10.)(=.(>.$?.$38.)(10.$?.$38.+<.^11.)(=.(>.$?.$38.)(10.$?.$38.+=.^12.)(=.(>.$?.$38.)(10.$?.$38.+>.^13.)(=.(>.$?.$38.)(10.$?.$38.+?.^14.)(=.(>.$?.$38.)(10.$?.$38.+10.^15.)(=.(>.$?.$38.)(10.$?.$38.+11.^16.)(=.(>.$?.$38.)(10.$?.$38.+1<.^17.)(=.(>.$?.$38.)(10.$?.$38.+1=.^18.)(=.(>.$?.$38.)(10.$?.$38.+1>.^19.)(=.(>.$?.$38.)(10.$?.$38.+1?.^1:.)(16.(>.$?.$38.)))))))))))))))))(=.$3:.(3;.(3<.^1.)&4.(3=.^2.)(3<.^9.)$37.)(=.$3:.(50.(3<.^5.)(3<.^4.))(16.$3:.)))(=.$45.(52.(3<.^<.)(3<.^1.))(16.$45.))(=.$1:.#0.(16.$1:.)))")
(* [comment removed for export] *).

Eval vm_compute in (su_wf (SUM_mlawA 4), su_nl (SUM_mlawA 4), su_nrl (SUM_mlawA 4), su_wf (SUM_amemsetWA 4 5), su_nl (SUM_amemsetWA 4 5), su_nrl (SUM_amemsetWA 4 5)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SGW.
  Context {HL : heap_layout}.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Variable GSX : list Z.
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis MLA : mpi_core_mla_stmtA asegs AL A_MPI_CORE_MLA.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0@L10351599025.113L17425393934.113L23423329468.113L25175738783.113L26684414795.113L32202401947.113L32765967378.153L35004282730.103L35118314922.103L45541955549.113L45910187748.138L48400057878.113L56083725980.113L56280291983.113L8446597963.113 00000\01K02?03_04J05A07607_08=09009g0;K0=80>10>\S1X1p1S3SPu2RA2ws2ss3PR64PR134PR234PR251i2HpS1X1p2dl1S2sl3SPu2RA2ws2ss3PR34PR144PR234PR251iS1X1p1S3SPu2RA2NS2ws2ss2LS3PR64PR134PR164PR234PR251iS1X1p2dl1S2sl1N3SPu2lo2RA2NS2ws2ss2LX2LS3PR63PR73PR83PR94PR134PR124PR174PR194PR204PR234PR251i2HpS1X1p2dl1S3SPu2RA2ws2ss3PR13PR24PR234PR251iS1X1p1S2sl3SPu2RA2NS2ws2ss2LS3PR64PR114PR134PR234PR251iS1X1p2dl1S2sl1N3SPu2lo2NS2ws2ss2LX2LS3PR13PR33PR62r43PR72r33PR84PR104PR114PR124PR174PR194PR202q01r1H2H02q43H192q53H24S1X1p2dl1S2sl3SPu2RA2ws2ss4PR134PR234PR25S1X1p1S3SPu2RA2ws2ss4PR234PR25S1X1p1S1N3SPu2RA2ws2ss2LX3PR64PR134PR154PR234PR251iS1X1p1S1N3SPu2RA2ws2ss2LX3PR64PR134PR234PR251i3ws'4LEN'S1X1p2dl1S2sl1N3SPu2lo2RA2NS2ws2ss2LX2LS3PR13PR63PR73PR83PR94PR134PR124PR144PR174PR194PR234PR251i2HpS1X1p2dl1S2sl1N3SPu2lo2RA2NS2ws2ss2LX2LS3PR13PR33PR63PR73PR83PR94PR104PR114PR134PR144PR174PR204PR234PR251i2HpS1X1p2dl1S1N3SPu2RA2ws2ss2LX3PR64PR104PR134PR234PR251i2HpS1X1p1S2sl3SPu2RA2ws2ss3PR33PR44PR234PR251i". (* [comment removed for export] *)
  Lemma sum_mlawA_validGX (kA : nat) (X : Z) : nth kA GS 0 = X -> summary_validG asegs AL GS (SUM_mlawA kA).
  Proof.
    intros GX. unfold SUM_mlawA, q. lx_sum_unfold.
    intros p dl S sl X0 N SPu lo RA NS sb.
    intros ws ss CS F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] SB MI GX' R10 R11 R12 R13 R2 R1 ST [HX LX] [HS LS] OD OS G1 G2.
    intros PR1 PR2 PR3 PR4 PR6 PR7 PR8 PR9 PR10 PR11 PR12 PR13 PR14 PR15 PR16 PR17 PR18 PR19 PR20 PR21 PR22 PR23 PR24 PR25 PR26.
    change (X0 = nth kA GS 0) in GX'. rewrite GX in GX'. subst X0.
    cbn in PR7, PR8, PR9, PR18, PR21.
    (* [comment removed for export] *)
    assert (OS' : aobj asegs AL CS m S (4 * Z.min dl sl)) by (eapply aobj_sub; [exact OS | lia | lia]).
    pose proof IMG as IMG'. unfold asan_img_ok in IMG'. destruct IMG' as (IG & ILO & IHI & IGSB).
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    assert (U1 : bv_unsigned x1 = RA) by (rewrite R1; apply uw64; assumption).
    assert (ABS : abase asegs AL m) by (split; [rewrite IG, IGSB; exact G1 | rewrite IGSB, <- SB; exact G2]).
    (* [comment removed for export] *)
    set (i := (p - X) / 4).
    assert (Hp : p = X + 4 * i) by (subst i; Z.div_mod_to_equations; lia).
    eapply evtA_cut.
    { eapply (lx_mla_windowA asegs AL A_MPI_CORE_MLA MLA CS x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m
                X i dl S sl lo ws ss);
        rewrite ?U2, ?U1, <- ?Hp; first [eassumption | lia | idtac]. }
    cbv beta. intros ms' POST. unfold lx_mla_window_postA, MPI_CORE_MLA_STACK_A in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ws' & -> & MU & WM & MI' & HX' & LEN' & FI & SK & ST').
    apply evtA_done. rewrite U2 in MU, ST'. rewrite <- Hp in MU.
    lx_sum_post.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sum_mlawA_okOX (kA : nat) (X : Z) : nth kA GS 0 = X -> forall OPS CS, summary_okO asegs AL GS OPS CS (SUM_mlawA kA).
  Proof. intros GX OPS CS. apply apply_summary_soundO, summary_validG_O, (sum_mlawA_validGX kA X GX). Qed.
End SGW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section SOXW.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Variables (GSX : list Z) (OPS : list (mem -> Prop)).
  Let GS : list Z := alloc_ceiling :: GSX.
  Hypothesis G1 : nth 1 GS 0 = htop asegs R HIA h.
  Hypothesis G2 : nth 2 GS 0 = arl_need_amem R.
  Hypothesis G3 : nth 3 GS 0 = arl_stklo R.
  Hypothesis O0 : nth 0 OPS (fun _ => True) = (fun m => HM asegs R HIA h LB LF m).
  Hypothesis AMS : arl_amemset R = 0x68258 \/ arl_memset_i R = 0x68258.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L1632069692.88  L34094807278.85 L4194688064.3   L45912036324.111L54818002485.88 L64082751029.111L66699322891.108L67543993069.11100000<00F00M00a00k01>01M01NS1V2ws2V02V1S1N2ws3LENS1N3NLOS1N2ws4LENB3ws'4LEN'S1N2ws3NHIS3DST1N2ws3ws'4LEN'S1N2ws3LEN4LENBF". (* [comment removed for export] *)
  Lemma sum_amemsetWA_okO (kd kn : nat) (DST N : Z) (CS : Z -> Prop) : ltac2:(CDefT.buildp (gd_tbl_LxAMpiSums ()) "P,(6.P,$?.Sp(53.$54.VR,VHIA,Vh,)O1.)P,(6.$?.(55.$?.O5.VGS,=)O3.)P,(6.$?.(55.$?.O4.VGS,=)O2.)P,(56.(57.VR,)(58.$59.VLB,(5:.VLF,))(5;.VR,)(5<.$54.VR,VHIA,Vh,)O3.(12.+4.O2.))(5=.$54.(5>.VR,)VGS,VOPS,O1.(5?.O5.O4.))")
(* [comment removed for export] *).
  Proof.
    intros ECS GD GN CW. subst CS. apply apply_summary_soundO.
    unfold SUM_amemsetWA, q; lx_sum_unfold.
    intros DSTp V NN SPu LO HT NA SL N0 A0 NG.
    intros ws F fc m.
    intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
    intros [CSOK ALWF] _ MI GD' GHT GNA GSL GN' R10 R11 R12 R2 ST [HDST LEN] OD EA0 ENG ENN V0 V1 NLO NHI SLLO LOSP SCR SEP SPTOP SP0 SP1 OQ0.
    change (DSTp = nth kd GS 0) in GD'; change (HT = nth 1 GS 0) in GHT; change (NA = nth 2 GS 0) in GNA; change (SL = nth 3 GS 0) in GSL; change (NG = nth kn GS 0) in GN';
    change (nth 0 OPS (fun _ => True) m) in OQ0.
    rewrite GD in GD'; rewrite G1 in GHT; rewrite G2 in GNA; rewrite G3 in GSL; rewrite GN in GN'; rewrite O0 in OQ0; cbv beta in OQ0.
    subst DSTp HT NA SL NN NG; subst A0. rewrite !ENG in *; clear ENG N0.
    assert (U2 : bv_unsigned x2 = SPu) by (rewrite R2; apply uw64; assumption).
    pose proof (u8arr_of_u32arr asegs m DST ws HDST) as HU.
    assert (LENB : Z.of_nat (length (u32s ws)) = 4 * N) by (rewrite u32s_length; lia).
    pose proof (cw_top47_or asegs R HIA h LB LF m (arl_stklo R) DST (4 * N) OQ0 CW ltac:(clear -NLO NHI; lia)) as HI.
    eapply evtA_cut;
    [ destruct AMS as [AE|AE];
      [ eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF DST V (4 * N) LO (u32s ws)); rewrite ?U2;
        first [ left; symmetry; exact AE | eassumption | cbn in *; lia ]
      | eapply (artA_amemset asegs R HIA 0x68258 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m h LB LF DST V (4 * N) LO (u32s ws)); rewrite ?U2;
        first [ right; symmetry; exact AE | eassumption | cbn in *; lia ] ]
    | cbv beta ].
    intros ms' POST; unfold call_postA in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & -> & HU' & ST' & HH').
    apply evtA_done; rewrite U2 in MU, ST'.
    destruct (u32arr_of_u8arr asegs m' DST _ (Z.to_nat N) HU' ltac:(rewrite repeat_length; lia)) as (ws' & HD' & LEN').
    lx_sum_post.
    all: try (lazymatch goal with |- ?f 0%nat OPS ?d ?mm => change (nth 0%nat OPS d mm); rewrite O0; cbv beta; exact HH' end).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SOXW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lxm_cw :=
  try (lazymatch goal with |- client_wrange ?L ?LBs ?lo ?top ?a ?n =>
         let a' := eval cbn [List.nth] in a in let n' := eval cbn [List.nth] in n in change (client_wrange L LBs lo top a' n') end);
  first [ assumption
        | match goal with K : client_wrange ?L ?LBs ?lo ?top ?a ?n |- client_wrange ?L ?LBs ?lo ?top ?a ?n' => replace n' with n by lia; exact K end
        | match goal with |- ?g => idtac "lxm_cw: cannot show" g; fail end ].
Ltac lxm_sum1 :=
  lazymatch goal with
  | |- summary_okO _ _ _ _ _ (SUM_mlawA _) =>
      eapply sum_mlawA_okOX; [> eassumption | first [ eassumption | apply A_mpi_core_mla_spec; eassumption ] | reflexivity ]
  | |- summary_okO _ _ _ _ _ (SUM_amemsetWA _ _) =>
      eapply sum_amemsetWA_okO;
      [> reflexivity | reflexivity | reflexivity | reflexivity
       | first [ left; assumption | right; assumption | left; symmetry; assumption | right; symmetry; assumption ]
       | first [ reflexivity | assumption | symmetry; assumption ] | reflexivity | reflexivity | lxm_cw ]
  | |- ?g => idtac "lxm_sum1: no ok-lemma for" g; fail
  end.
Ltac lxm_sums SUMS OBJS :=
  let mx := lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx end in
  lazymatch goal with
  | H : lx_opq _ _ _ (fun m => HM ?segs ?R ?HIA ?h ?LB ?LF m) _ _ mx |- evtA _ ?AL ?CS _ _ =>
      let OPS := constr:(@cons (mem -> Prop) (fun m => HM segs R HIA h LB LF m) (@nil (mem -> Prop))) in
      let GS := constr:(@cons Z (@alloc_ceiling (arl_L R)) (@cons Z (htop segs R HIA h) (@cons Z (arl_need_amem R) (@cons Z (arl_stklo R) OBJS)))) in
      let HS := fresh "LXSUMS" in
      assert (HS : List.Forall (summary_okO segs AL GS OPS CS) SUMS)
        by (repeat (apply List.Forall_cons; [ lxm_sum1 | ]); apply List.Forall_nil)
  | |- _ => fail "lxm_sums: no lx_opq HM fact at the goal memory (run lxr_pose first) / not an evtA goal"
  end.
