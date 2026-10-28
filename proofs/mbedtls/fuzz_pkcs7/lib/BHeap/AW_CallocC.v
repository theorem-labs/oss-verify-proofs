(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_AllocA AW_DepotA AW_Poison AW_AllocB AW_MallocB AW_MallocC AW_CallocA AW_CallocB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_CallocC () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.A_ALLOCATE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CallocA.A_PC_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.max"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocC.msegA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.CallocC.csegA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CallocA.A_CALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "Stdlib.ZArith.BinInt.Z.shiftr"; "ARUN_1.CallocC.SegB.csegC1_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "ARUN_1.CallocC.SegB.csegC2_post"].

Section ARUN_1. Context {hAR : arun}.

Section CallocC.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition csegA_post (SP : Z) (gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 : word) (F : bvmap 5 word) (fc : bv 32)
      (cnt sz n lo T TOP d : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocC ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lws,(4.(2.&40.))(1.$5.Lsize,$5.(1.(4.(2.&8.))Lfr1,(4.(2.&8.))(1.(4.(2.&8.))Lfr2,(4.(2.&8.))(1.(4.(2.&8.))Lfr3,(4.(2.&8.))(1.(4.(2.&8.))Lfr4,(4.(2.&8.))ZSTK,$5.(6.O19.-858.)(7.(8.$0.R12.(9.(:.(;.&40.+48470.)(;.&40.(6.R1.-38.))O18.(;.&40.$<.)R11.R10.R?.(;.&40.O6.)(;.&40.R1.)(;.&40.$=.)(;.&40.O6.)(;.&40.+8.)(;.&40.R1.)(;.&40.+1.)(;.&40.=)R>.R=.(;.&40.$=.)(;.&40.+1.)(;.&40.+1.)(;.&40.R1.)(;.&40.(6.O19.-59.))O12.O11.O10.O?.O>.R<.R;.R:.R9.)O:.(;.&40.$>.)O9.(?.(2.&40.))R8.(10.$11.)))(7.(12.(13.(14.$5.$5.)(15.$5.$5.O5.O19.)(13.(14.$5.$5.)(15.$5.$5.(6.O4.+<60.)(6.O4.+<61.))(16.(14.$5.$5.))))O1.R8.)(7.(17.$11.O1.R8.)(7.(18.$11.R8.)(7.(19.$11.R8.(6.O19.-40.)(13.$1:.(1;.O13.)(13.$1:.(1;.O14.)(13.$1:.(1;.O15.)(13.$1:.(1;.O16.)(13.$1:.(1;.O17.)(13.$1:.(1;.O;.)(13.$1:.(1;.O<.)(13.$1:.(1;.O=.)(16.$1:.))))))))))(7.(19.$11.R8.R1.(13.$1:.(1;.(;.&40.(6.R1.+10.)))(13.$1:.(1;.(;.&40.R6.))(16.$1:.))))(7.(1<.$11.R8.(6.R1.+10.)R7.)(7.(8.$1=.(1>.(2.&40.)R7.)#1>.)(7.(7.(1?.+1.R6.)(1?.R6.+1>.))(7.(1?.R6.(6.O2.+2.))(7.(19.$11.R8.(6.R1.+100.)(13.$1:.(20.#708.R5.)(16.$1:.)))(7.(19.$11.R8.(6.R1.+808.)(13.$1:.(1;.(;.&40.O19.))(16.$1:.)))(7.(19.$11.R8.(6.R1.+810.)(13.$1:.(20.#8.R4.)(16.$1:.)))(7.(19.$11.R8.(6.R1.-8.)(13.$1:.(20.#8.R3.)(16.$1:.)))(7.(19.$11.R8.(6.R1.-38.)(13.$1:.(20.#8.R2.)(13.$1:.(1;.(;.&40.$21.))(13.$1:.(1;.(;.&40.O8.))(13.$1:.(1;.(;.&40.O7.))(13.$1:.(1;.(;.&40.O19.))(13.$1:.(1;.(;.&40.+699<4.))(16.$1:.))))))))(7.(19.$11.R8.(6.O4.+<60.)(13.$1:.(22.(;.&8.=))(16.$1:.)))(7.(23.$11.R8.O5.(6.R1.-38.))(23.$11.R8.(6.O19.-10.)(24.O3.O19.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01R0@L10268361782.5  L1098965441.143 L11312779374.6  L11520233656.2  L13266555807.5  L14002794803.7  L14602434450.3  L14883623720.3  L15513725702.2  L16555544494.3  L1665585555.7   L19295369323.5  L20565690987.5  L21989683525.114L22704456280.5  L22706556809.6  L23411935237.8  L23749077557.7  L23761187578.5  L24892837319.2  L24897143244.10 L25858816235.5  L259223070.138  L25952359058.3  L25984553605.8  L261493381.111  L26291035175.2  L27848808849.2  L28317027333.0  L29189557397.113L29189557397.114L30035708878.6  L30449887874.5  L30833920179.7  L3138120371.7   L35518591711.3  L36262250517.7  L36438198037.7  L36841451887.5  L37682279081.10 L37685743390.3  L37824690451.7  L37888894965.7  L38235734261.1  L38637156310.6  L39077983678.2  L39212163293.8  L39831478948.2  L40209243729.2  L407260245.7    L42079078456.2  L42080671941.7  L42155231742.3  L42833409668.5  L44099045317.7  L44101916472.2  L45134552723.7  L46156896021.7  L46336856945.9  L47216798497.0  L47868035168.8  L48446870377.144L48562303429.8  L48711619285.7  L48955120189.3  L48992309230.144L5304054668.1   L53763977155.7  L53766455102.2  L5429770831.4   L55961781779.7  L56109162145.7  L56203711877.7  L5780586706.7   L57864511827.3  L583080789.7    L59869075256.2  L60805037525.2  L61031298631.9  L61073965891.7  L61075690430.2  L61364978515.3  L62415520029.111L62422007174.138L6266751827.7   L62835699605.7  L62984661301.7  L64137815251.7  L65092451413.7  L65104223396.2  L66006464133.8  L66240431488.7  L66568461826.7  L67046461077.7  L68231271950.10 L8806423751.6   L9794277250.2   L9845264484.6   00000?00U00n01501B01\01k02602>02I02Q02d03703E03X03f04804R04g04k05305F05\05g06106?06F06M06N06\06j07D07Z08408N08Y08a08i09609[09k0:30:M0:Q0:e0:l0;:0;D0;J0;R0;Y0;d0<20<G0<R0<Y0<a0<i0=C0=D0=g0>=0>O0>W0>b0?80?<0?G0?N0?W0?_0?j0@50@N0@Y0@a0@h0A00A80AC0AJ0AU0Ac0B90BA0BI0Bc0Bk0C30C=0CO0Ci0D?0DG0DT0Df0Dj0E@S2SP3TOP1x2Hx1HS3hAR2SP2ws2HL3ws23HL2S3hAR2SP2lo5LOIMG3SPL3SPHS2SP2loS2SP2lo1A1k1HS3hAR2SP2lo1T2T15LOIMG3SPLS3TOP4TOP04TOP1S2SP2lo3SPLS2SP3SPHS2SP3TOP2GTS3hAR2SPS3hAR2lo1T2T15LOIMGS3hAR2lo1T2T15LOIMGS3hAR2SP2ws2HLS2SP2lo4TOPU2a'3Ha'S2SP2lo1T1x2HxS2SP2lo3SPL1A1k2H1S3hAR2SP2lo1T2T15LOIMG3SPLS3hAR2SP2lo5LOIMG3SPLS2SPS3hAR2SPS3hAR2lo1T2T15LOIMGS3hAR2SP2ws2HL3ws23HL2S2SP2lo3TOPS1T1A1k2H2S3hAR2SP2ws2HLS2SP2loS2SP2loSS3hAR2SP2ws2HLS3hAR2SP2ws2HLS3hAR2SP2lo4TOP25LOIMG3SPLS3hAR2lo3CTX3CX15LOIMGS3hAR2SP2lo1T2T15LOIMG3SPLS3hAR2SP2lo1T2T15LOIMG3SPLS2SP2lo3TOPS3hAR2SPS3hAR2SPS2SP2lo1A1k1HS3hAR2SP2lo1T3CTX3TOP2T13CX12TC5LOIMGS3TOP4TOPU5TOPUBS3hAR2SPS3hAR2SP2lo1T2T15LOIMG3SPLS2loS3hAR2lo5LOIMG1A1k1HS2SP2loS2SP2lo1A1k2H1S4size3SZBS1n2NBS3hAR2SPS2SP2loS3hAR2SP2loS3hAR2lo5LOIMGS3hAR2SP2lo5LOIMG3SPLS3hAR2SP2loS2SP2loS3hAR2SPS3hAR2SPS3hAR2SP2lo4TOP25LOIMG3SPLSS3hAR2SP2lo3TOP4TOP14TOP25LOIMG3SPLS3hAR2SP2ws2HL3ws23HL2S2SP2lo3SPL1A1k2H1S3hAR2SPS2SP3TOP2LES3hAR2SP2ws2HL3ws23HL2S2SPS3hAR2SP2loS2SP2loS2SP4TOP2S3hAR2SPS3hAR2SP2loS3hAR2SP2loS3hAR1T3CTX2T02T13CX03CX1S2SP2lo3SPLS3hAR2SPS2SP2loS2SP3TOPS3hAR2SPS3hAR2SP2loS2SP2loS2SP2lo3SPLS3hAR2SP2ws2HLS3hAR2SP2ws2HL3ws23HL2S3hAR2SPS3hAR2SPS3hAR2SP2lo1T2T15LOIMG3SPLS3hAR2SPS3hAR2SPS4size3SZBS2SP2lo3SPL1A1k2H1S3hAR2SP2lo1T2T15LOIMG3SPLS2SP2lo3TOP3SPL1x2Hx1HS3hAR2SPS3hAR2SP1q2HqS2SP2lo1T3SPL1x2HxS2SPS3hAR2SP2lo1T2T15LOIMG". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma csegA : ltac2:(CDefT.buildp (gd_tbl_AW_CallocC ()) "Pra,(2.&40.)Pgp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$5.Pcnt,$5.Psz,$5.Pn,$5.Plo,$5.PT,$5.PCTX,$5.PTOP,$5.PLO,$5.PTOPU,$5.Pd,$5.PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(7.(1?.=R=.)(26.R=.(27.+2.+40.)))P,(7.(1?.=R=.)(26.R=.(27.+2.+40.)))P,(8.$5.R=.(28.R?.R>.))P,(7.(1?.=R>.)(26.R>.(27.+2.+20.)))P,(29.$11.R5.R:.R9.(2:.&40.R28.)R12.R8.)P,(1?.R;.R13.)P,(7.(1?.R=.R;.)(1?.R;.(27.+2.+40.)))P,(2;.R8.R10.R?.)P,(2<.$11.R9.(6.R11.+8.)(13.$1:.(1;.(;.&40.R?.))(13.$1:.(1;.(;.&40.(2=.R?.(27.+2.+17.))))(16.$1:.))))P,(2<.$11.R:.(6.R12.+28.)(13.$1:.(22.(;.&8.=))(16.$1:.)))P,(19.$11.R;.(6.R13.+<60.)(13.$1:.(22.(;.&8.=))(16.$1:.)))P,(1?.(27.+2.+17.)R12.)P,(1?.R13.(27.+2.+2?.))P,(1?.(6.R1;.+10.)(27.+2.+2?.))P,(7.(1?.+1000.R17.)(2>.(1?.(6.R17.+1000.)+10000.)(1?.+65?000.R17.)))P,(1?.(6.R18.+1000.)(2?.VhAR,))P,(1?.+65?000.R18.)P,(1?.(6.R19.+10000.)(2?.VhAR,))P,(2>.(1?.(6.R1;.+1000.)R1:.)(1?.(6.R1:.+10000.)R1;.))P,(30.VCS,R1<.+1000.)P,(30.VCS,R1<.+10000.)P,(23.$11.R16.R23.R1<.)P,(30.VCS,R24.(2=.R1=.R24.))P,(23.$11.R18.R21.R25.)P,(1?.(2?.VhAR,)R22.)P,(1?.R23.(2=.R27.+1000.))P,(8.$5.(31.R28.+10.)=)P,(30.VCS,R25.(2=.R29.R25.))P,(18.$11.R1=.)(32.$11.VAL,VCS,(33.R2;.R45.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R46.R41.R40.R20.R1?.R2:.R29.R28.R27.R26.R24.R21.R1>.)(9.(:.R46.(;.&40.R2;.)R45.(;.&40.$<.)R44.R43.R42.R41.R40.(;.&40.R2:.)(;.&40.R29.)R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.)R20.(;.&40.$34.)R1?.(?.(2.&40.))R1>.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP cnt sz n lo T CTX TOP LO TOPU d F fc m
      CB0 SZ0 EN NB CH0 LOB TOPUB MS8 THR TSW UNW TOP0 TOP1 TOP2 T0 T1 CX0 CX1 TC TCS CTXCS STT STCS ST LOIMG SPL SPA SCS MI.
    pose proof (u64_range s0) as S0R.
    facts. dpose MS8 as (INI & MCS & GOTF & FU & GOT & PGS & TSD & TPC & TSA & CTH).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (calloc_pro AL IMG ALWF CS CSOK); try eassumption. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m1 & ws & fr1 & fr2 & fr3 & -> & MU1 & WM1 & MI1 & FR8 & STKC & HTR & HL & F1800 & TFB & F8 & FJ & ST1)).
    assert (LO1 : forall A k, A + k <= lo -> disjoint_from [(lo, SP)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
    assert (MS1 : msegA_statics m1 T CTX).
    { eapply (msegA_statics_transport _ m m1 T CTX MS8 MU1); [intros A k H; apply LO1; clear - H LOIMG; lia| apply LO1; clear - CX1 LOIMG; lia]. }
    dpose MS1 as (INI1 & MCS1 & GOTF1 & FU1 & GOT1 & PGS1 & TSD1 & TPC1 & TSA1 & CTH1).
    assert (THR1 : ro_cells asegs m1 (T + 8) [C8 (Z_to_bv 64 TOP); C8 (Z_to_bv 64 (TOP - 2^23))])
      by (eapply ro_cells_transport; [exact THR| exact MU1| apply LO1; cbn; clear - T1 LOIMG; lia]).
    assert (TSW1 : ro_cells asegs m1 (T + 40) [C1 (Z_to_bv 8 0)])
      by (eapply ro_cells_transport; [exact TSW| exact MU1| apply LO1; cbn; clear - T1 LOIMG; lia]).
    assert (UNW1 : rw_cells asegs m1 (T + 3168) [C1 (Z_to_bv 8 0)])
      by (eapply rw_cells_transport; [exact UNW| exact MU1| exact WM1| apply LO1; cbn; clear - T1 LOIMG; lia]).
    assert (STT1 : stk asegs m1 SP TOP)
      by (eapply stk_transport_disjoint; [exact STT| exact MU1| exact WM1| cbn [disjoint_from]; clear; lia]).
    clear INI MCS GOTF FU GOT PGS TSD TPC TSA CTH THR TSW UNW STT MS8.
    (* [comment removed for export] *)
    pose proof (proj1 (rw_cells_app asegs m1 (SP + -2136) [C8 _] _) STKC) as [SK0 SK1]. cbn [cells_size csize Nat.add] in SK1.
    pose proof (proj1 (rw_cells_app asegs m1 _ [C4 _] _) SK1) as [SK8 SK12]. cbn [cells_size csize Nat.add] in SK12. clear STKC SK1.
    replace (SP + -2136 + Z.of_nat 8) with (SP + -2136 + 8) in SK8 by lia. replace (SP + -2136 + Z.of_nat 8 + Z.of_nat 4) with (SP + -2136 + 12) in SK12 by lia.
    (* [comment removed for export] *)
    assert (STT1' : stk asegs m1 SP (Z.max TOP SP)).
    { destruct (Z.le_gt_cases SP TOP) as [LE|GT]; [rewrite Z.max_l by (clear - LE; lia); exact STT1| rewrite Z.max_r by (clear - GT; lia); apply stk_empty; clear - TOP2 LOIMG SPL; lia]. }
    assert (SR1 : stk asegs m1 (SP + -16) (Z.max TOP SP)).
    { eapply stk_merge; [| exact STT1'| clear; lia].
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FR8) as [_ FRhi].
      cbn [cells_size csize Nat.add] in FRhi. replace (SP + -64 + Z.of_nat 48) with (SP + -16) in FRhi by lia.
      pose proof (stk_of_rw_cells asegs m1 (SP + -16) _ FRhi) as X. cbn [cells_size csize Nat.add] in X.
      replace (SP + -16 + Z.of_nat 16) with SP in X by lia. exact X. }
    (* [comment removed for export] *)
    assert (LNK1 : ro_cells asegs m1 (SP + -16) [C8 (Z_to_bv 64 (bv_unsigned s0))]).
    { rewrite Z_to_bv_bv_unsigned.
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FR8) as [_ FRhi].
      cbn [cells_size csize Nat.add] in FRhi. replace (SP + -64 + Z.of_nat 48) with (SP + -16) in FRhi by lia.
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -16) [C8 s0] [C8 ra]) FRhi) as [[X _] _]. exact X. }
    assert (CH1 : uwc asegs m1 LO TOPU (bv_unsigned s0) SP d).
    { eapply (uwc_munch asegs [(lo, SP)]); [exact CH0| exact MU1| clear - LOIMG SPL; lia| clear - TOPUB; lia| intros a' Ha'; cbn; clear - Ha'; lia]. }
    clear CH0.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (unwind_impl_spec AL IMG ALWF CS CSOK (SP + -2136) A_PC_CALLOC SP TOP (TOP - 2^23) (SP + -16) (Z.max TOP SP) T CTX) with (LO := LO) (TOPU := TOPU);
        [ | | | | | | | | | | | exact LOB | exact TOPUB | clear - T1 LOIMG SPL; lia | exact HL | exact SK8 | exact HTR | exact TFB | exact SR1 | exact LNK1 | exact CH1 | exact S0R | exact GOT1 | exact PGS1 | exact INI1 | exact TSD1 | exact TPC1 | exact TSA1 | exact CTH1 | exact THR1 | exact TSW1 | exact UNW1 | exact ST1 | clear - LOIMG; lia | clear - SPL; lia | clear; lia | | exact MI1 | reflexivity ].
      - clear - TOP2 TOP1 LOIMG SPL. lia.
      - intros x Hx. destruct (Z.lt_ge_cases x SP); [apply SCS; clear - Hx H SPL; lia| apply STCS; clear - Hx H; lia].
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear - SPL; lia| clear; lia].
      - clear - LOIMG SPL; lia.
      - clear - TOP0 TOP1; lia.
      - unfold A_PC_CALLOC. clear; lia.
      - clear - TOP1 TOP2 LOIMG SPL SPA. split; [lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as [q Hq]. exists (2 * q). lia.
      - exact TCS. - exact CTXCS.
      - clear - T0 T1 CX0 CX1. lia.
      - clear - T1 CX1 TC LOIMG. lia.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
    cbn beta. (intros ms2 dd_H; ddestruct dd_H as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ws2 & size & -> &
                          MU2 & WM2 & MI2 & SZ2 & HTR2 & TFB2 & UNW2 & SZB & SZD & HL2 & ST2 & SR2)).
    replace (ret_pc (Z_to_bv 64 0x699b0)) with (Z_to_bv 64 0x699b0) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    zstep. zstep. replace (SP + -2048 + -88) with (SP + -2136) by lia. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (DJ2 : forall A k, (A + k <= lo \/ SP + -2136 + 2064 <= A) -> (A + k <= T + 3168 \/ T + 3169 <= A) ->
              disjoint_from [(SP + -2136 + 8, SP + -2136 + 12); (SP + -2136 + 16, SP + -2136 + 256); (SP + -2136 + 2056, SP + -2136 + 2064); (T + 3168, T + 3169); (lo, SP + -2144)] A k).
    { intros A k H1 H2. cbn [disjoint_from]. clear - H1 H2 SPL. repeat split; lia. }
    assert (FR8' : rw_cells asegs m2 (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR8| exact MU2| exact WM2| apply DJ2; cbn; clear - T1 LOIMG SPL; lia]).
    assert (SK0' : rw_cells asegs m2 (SP + -2136) [C8 (Z_to_bv 64 (SP + -2136 + 16))]).
    { eapply rw_cells_transport; [exact SK0| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL T1 LOIMG. repeat split; lia. }
    assert (SK12' : rw_cells asegs m2 (SP + -2136 + 12) [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact SK12| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL T1 LOIMG. repeat split; lia. }
    assert (F1800' : rw_cells asegs m2 (SP + -2136 + 256) [CB 1800 fr1])
      by (eapply rw_cells_transport; [exact F1800| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    assert (F8' : rw_cells asegs m2 (SP + -2136 + 2064) [CB 8 fr2])
      by (eapply rw_cells_transport; [exact F8| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    assert (FJ' : rw_cells asegs m2 (SP + -2144) [CB 8 fr3])
      by (eapply rw_cells_transport; [exact FJ| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    clear FR8 SK0 SK12 F1800 F8 FJ SK8 HTR TFB SR1 STT1 ST1 UNW1.
    (* [comment removed for export] *)
    assert (STKC : rw_cells asegs m2 (SP + -2136) [C8 (Z_to_bv 64 (SP + -2136 + 16)); C8 (Z_to_bv 64 size)]).
    { apply (proj2 (rw_cells_app asegs m2 (SP + -2136) [C8 _] [C8 _])). split; [exact SK0'|]. cbn [cells_size csize Nat.add].
      eapply (rw_cells_reshape asegs m2 _ [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 0)]).
      - apply (proj2 (rw_cells_app asegs m2 _ [C4 _] [C4 _])). split; [replace (SP + -2136 + Z.of_nat 8) with (SP + -2136 + 8) by lia; exact SZ2|].
        cbn [cells_size csize Nat.add]. replace (SP + -2136 + Z.of_nat 8 + Z.of_nat 4) with (SP + -2136 + 12) by lia. exact SK12'.
      - cbn. tauto.
      - cbn [cells_bytes cbytes]. rewrite (le8_split4 (Z_to_bv 64 size)). rewrite unsigned_lit by (clear - SZB; lia).
        rewrite Z.div_small by (clear - SZB; lia). rewrite <- app_assoc. reflexivity. }
    clear SK0' SK12' SZ2.
    (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (acalloc_pro AL IMG ALWF CS CSOK); [exact CB0| exact SZ0| exact EN| clear - NB; lia| clear - SPL LOIMG SPH; lia| exact ST2| exact LOIMG| clear - SPL; lia| clear - SPH; lia| | | exact MI2].
      - clear - SPA. replace (SP + -2144) with (SP + (-134) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
    cbn beta. (intros ms3 dd_H; ddestruct dd_H as (m3 & fr4 & -> & MU3 & WM3 & MI3 & AFR & ST3)).
    replace (SP + -2144 + -48) with (SP + -2136 + -56) in * by lia.
    unfold csegA_post. deexists 9. dexists m3, ws2, size, fr1, fr2, fr3, fr4.
    split; [reflexivity|].
    assert (LO3 : forall A k, (A + k <= lo \/ SP + -2144 <= A) -> disjoint_from [(lo, SP + -2144)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
    split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
             eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear - SPL. intros x Hx. lia. }
             eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear - SPL. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|].
    split; [eapply rw_cells_transport; [exact FR8'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact STKC| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply u64arr_transport; [exact HTR2| exact MU3| exact WM3| apply LO3; rewrite HL2; cbn; clear; lia]|].
    split; [exact HL2|]. split; [exact SZB|]. split; [exact SZD|].
    split; [eapply rw_cells_transport; [exact F1800'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact TFB2| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact F8'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [replace (SP + -2136 + -8) with (SP + -2144) by lia; eapply rw_cells_transport; [exact FJ'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [exact AFR|].
    split; [eapply rw_cells_transport; [exact UNW2| exact MU3| exact WM3| apply LO3; cbn; clear - T1 LOIMG; lia]|].
    split; [exact ST3|].
    eapply stk_transport_disjoint; [exact SR2| exact MU3| exact WM3| apply LO3; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Section SegB.
    Variables (SP n lo T CTX TID SB cnt csz : Z) (pw : word).
    Let STK := SP + -2136.
    Let SPA := SP + -2136 + -56.            (* [comment removed for export] *)
    Let c := class_of (needed2 n).
    Let AB := SB + c * 2^32 + 16 * (bv_unsigned pw mod 2^32).
    Let UB := AB + rz_size n.
    Let CHB := AB + rz_size n + -16.
    Hypothesis NB : 0 <= n < 2^32.
    Hypothesis FP : from_primary n = true.
    Hypothesis LOIMG : ACEIL <= lo.
    Hypothesis SPL : lo <= SP - 4096.
    Hypothesis SPH : SP + 16 <= 2^47.
    Hypothesis SPA16 : SP mod 16 = 0.
    Hypothesis T0 : Timg T. Hypothesis T1 : T + 4096 <= ACEIL. Hypothesis TAL : T mod 4096 = 0.
    Hypothesis CX0 : 0x65f000 <= CTX. Hypothesis CX1 : CTX + 0x10000 <= ACEIL.
    Hypothesis TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T.
    Hypothesis TIDB : 0 <= TID < 2^31.
    Hypothesis SB0 : 0 <= SB. Hypothesis SB1 : SB + 2^37 < 2^47. Hypothesis SBAL : SB mod 4096 = 0.
    Hypothesis HCNT : 1 <= cnt <= 16. Hypothesis HCSZ : 0 <= csz < 2^64.
    Hypothesis AB0 : 0x65f000 <= AB. Hypothesis AB1 : AB + needed2 n <= ACEIL.
    Hypothesis ABT : AB + needed2 n <= T \/ T + 4096 <= AB.
    Hypothesis ABC : AB + needed2 n <= CTX \/ CTX + 0x10000 <= AB.
    Hypothesis ASB : al_sb AL = 0x7fff8000.
    Hypothesis TNS : T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T.
    Hypothesis CTXNS : CTX + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L27705381220.6 L61035084364.49L63368316718.5000000?00i01SS1n3FP'1H2H02H1S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB0S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB0". (* [comment removed for export] *)
    #[using="hAR SP T SB pw STK SPA c AB UB CHB FP SB0"] Lemma needed2_primary : needed2 n = needed n /\ 24 <= needed n <= 0x10000.
    Proof.
      pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
      unfold needed2. rewrite FP. split; [reflexivity|].
      unfold needed, rounded, round_up in *. pose proof (rz_size_bound n).
      pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
      clear - H H0 H1 NB FP'. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18941319889.46L8366240569.6  00000W00iS3hAR2SP1n1T2SB2pw3STK3SPA1c2UB3CHB3SB0S1n2SB2pw1c4SBAL1H". (* [comment removed for export] *)
    #[using="hAR SP T STK SPA UB CHB SB0 SBAL"] Lemma AB_al : AB mod 16 = 0.
    Proof.
      subst AB. pose proof (Z.div_mod SB 4096 ltac:(lia)).
      replace (SB + c * 2^32 + 16 * (bv_unsigned pw mod 2^32)) with ((SB / 4096 * 256 + c * 2^28 + bv_unsigned pw mod 2^32) * 16) by (clear - H SBAL; lia).
      apply Z_mod_mult.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Let SUB := 0x7fff8000 + UB / 8.                                  (* [comment removed for export] *)
    Let PGS := 0x7fff8000 + Z.shiftr (UB + nfix n / 8 * 8) 3.         (* [comment removed for export] *)
    Let KF := Z.min (nfix n) 4096.                                    (* [comment removed for export] *)

    Definition csegC1_post (gp : word) (F : bvmap 5 word) (fc : bv 32) (id : Z) (b0 : byte) (b1 : Z) (q6 q7 q8 q9 q10 q11 : word) (fr0 : list byte) (pgb : byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocC ()) "Lms',$0.(1.(2.&40.)Lx1,(2.&40.)(1.(2.&40.)Lx5,(2.&40.)(1.(2.&40.)Lx6,(2.&40.)(1.(2.&40.)Lx7,(2.&40.)(1.(2.&40.)Lx10,(2.&40.)(1.(2.&40.)Lx11,(2.&40.)(1.(2.&40.)Lx12,(2.&40.)(1.(2.&40.)Lx13,(2.&40.)(1.(2.&40.)Lx14,(2.&40.)(1.(2.&40.)Lx15,(2.&40.)(1.(2.&40.)Lx16,(2.&40.)(1.(2.&40.)Lx17,(2.&40.)(1.(2.&40.)Lx22,(2.&40.)(1.(2.&40.)Ly28,(2.&40.)(1.(2.&40.)Ly29,(2.&40.)(1.(2.&40.)Ly30,(2.&40.)(1.(2.&40.)Ly31,(2.&40.)(1.(2.&40.)Lj0,(2.&40.)(1.(2.&40.)Lj1,(2.&40.)(1.(2.&40.)Lj2,(2.&40.)(1.(4.(2.&40.))Lbs,(4.(2.&40.))(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(7.(8.$0.R17.(9.(:.R16.(;.&40.(6.VSPA,-80.))O?.(;.&40.$<.)R15.R14.R13.(;.&40.+1.)(;.&40.(35.Vn,))R12.R11.R10.R?.R>.R=.R<.R;.(;.&40.VAB,)(;.&40.(36.Vn,))(;.&40.VUB,)(;.&40.VCHB,)R:.(;.&40.VSTK,)(;.&40.(28.VTID,(27.+2.+20.)))(;.&40.(6.VUB,(35.Vn,)))(;.&40.VT,)(;.&40.+1.)R9.R8.R7.R6.)O>.(;.&40.+48174.)O=.(?.(2.&40.))R1.(10.$11.)))(7.(12.(13.(14.$5.$5.)(15.$5.$5.Vlo,(6.VSPA,-80.))(13.(14.$5.$5.)(15.$5.$5.(6.VCHB,+8.)(6.VCHB,+10.))(13.(14.$5.$5.)(15.$5.$5.VSUB,(6.VSUB,(37.(35.Vn,)+8.)))(13.(14.$5.$5.)(15.$5.$5.VPGS,(6.VPGS,+1.))(13.(14.$5.$5.)(15.$5.$5.(6.VT,+:?0.)(6.VT,+<60.))(16.(14.$5.$5.)))))))O1.R1.)(7.(17.$11.O1.R1.)(7.(18.$11.R1.)(7.(38.R1.VSPA,O3.=(;.&40.+48470.)(;.&40.Vn,)(;.&40.VSTK,)(;.&40.$=.)(;.&40.+1.)(;.&40.+1.)(;.&40.VSTK,)(;.&40.(6.VSP,-59.))O8.O7.O6.O5.O4.)(7.(19.$11.R1.VCHB,(13.$1:.(22.O;.)(13.$1:.(22.(;.&8.O:.))(13.$1:.(39.(;.&40.=))(13.$1:.(3:.(;.&40.(35.Vn,)))(13.$1:.(1;.(;.&40.(3;.(28.VTID,(27.+2.+20.))O<.)))(16.$1:.)))))))(7.(19.$11.R1.VSUB,(13.$1:.(20.(3<.(37.(35.Vn,)+8.))(3=.(2.&8.)(;.&8.=)(3<.(37.(35.Vn,)+8.))))(16.$1:.)))(7.(19.$11.R1.VPGS,(13.$1:.(22.(3>.Vn,O2.))(16.$1:.)))(7.(19.$11.R1.(6.VT,+:?0.)(13.$1:.(1;.R5.)(13.$1:.(1;.R4.)(13.$1:.(1;.R3.)(16.$1:.)))))(7.(1<.$11.R1.(6.VT,+;60.)R2.)(7.(8.$1=.(1>.(2.&40.)R2.)#20.)(23.$11.R1.Vlo,(6.VSPA,-80.)))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "01>0@L11019910313.28 L17054810462.24 L17135840957.24 L17784337564.19 L17882144120.26 L17882144120.28 L18607870801.24 L1905712448.19  L20302704847.28 L20573562197.28 L24886869106.145L24888640626.2  L24892837879.144L25320086065.28 L26069473972.27 L26275543149.2  L26631980436.24 L26631980436.28 L26876610421.24 L27697017043.3  L27705282402.5  L27848808849.2  L27991817377.3  L29786611176.10 L30862299178.24 L31659743062.2  L31736811297.28 L32045839665.28 L33128195209.19 L33292228550.19 L35243480162.26 L35243480162.27 L35243480162.28 L36193165570.2  L36786030869.28 L37881827237.26 L37881827237.27 L38235734261.1  L41008920023.19 L41864096740.8  L42198818825.19 L43089499825.19 L4323479075.28  L44345069824.10 L44355359517.19 L48535100989.24 L49301304837.26 L49301304837.27 L50627793533.24 L5172934059.24  L52016865498.28 L52481722021.27 L52657554222.19 L54497593123.28 L5629348309.24  L5629348309.26  L5629348309.27  L56319789689.24 L56393501986.19 L5808104861.19  L59619421015.27 L60525725327.28 L61030844230.119L61030858054.118L62099666698.24 L62727817027.28 L63221451435.27 L63370229784.120L63374621462.119L6425622916.19  L65181476846.0  L67266171279.28 L68053897848.26 L68053897848.28 L68489403102.24 L6913313913.19  L8936406121.26  L8936406121.27  00000\01:01Z02702e03S04604T05D05i06R06V07?07k08Y08a09H09o0:X0:c0:k0;20;=0;K0;g0;k0<T0=@0=]0>L0?30?Z0@A0@D0@n0A^0BL0BP0C20CL0Ci0DF0Dk0EK0F00FP0G50GZ0H70H^0IF0In0JO0K40KL0Kd0L<0M20MT0N10N[0OC0P>0Q90QU0R20Rh0Sc0T^0U?0U@0Uh0VV0WD0Wb0XC0Xf0YIS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS2H32H43SHR2H5S3hAR2SP1n2SB2pw3SPA1c2AB1H2H1S3hAR2SP1n2lo2SB2pw3SPA1c2AB3H12S3hAR2SP1n2SB2pw3SPA1c2AB3AB0S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2lo2SB2pw1c2AB3SPL2H43H12S3hAR2SP1n2SB2pw3SPA1c2AB4RZSBS3hAR2SP1n3CTX2SB2pw3SPA1c2AB5CTXNS3SHR2H32H42H5S3hAR2SP1n1T2SB2pw3SPA1c2AB2T01A1k2HkS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB3SB02bs2HLS2SPS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB3SB02bs2HLS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS3SHR2H32H42H5S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H02H22H83H12S2SP3SPHS3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR2H43H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB2H43H123SHRS3hAR2SP1n2lo2SB2pw1c2AB3SPL2H02H22H83H12S1n3N2E3NDBS1n1H2H0S2SP2loS2SP2lo3SPLS1n2SB2pw1c2ABS3hAR2SP1n2SB2pw3SPA1c2AB2H3S2SPS3hAR2SP1n3CTX2SB2pw3SPA1c2AB5CTXNS2H32H4S3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS3SHR2H32H42H5S3hAR2SP1n2SB2pw3SPA1c2AB3NFBS3hAR2SP1n2SB2pw3SPA1c2AB4RZSB3NFB3N2B3MNF4RNG'S3hAR2SP1n2lo2SB2pw3SPA1c2AB1A1k2Hk3H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB1A1k2Hk3H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB1A1k2Hk3H12S1nS3hAR2SP1n3CTX2SB2pw3SPA1c2AB3ABC2H12H02H8S3hAR2SP1n2lo1T2SB2pw1c2AB2T12H12H02H22H82H93H12S3hAR2SP1n2lo1T2SB2pw1c2AB3SPL2T12H12H02H23H12S2loS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMGS3hAR1n2SB2pw1c2AB3AB13RNGS3hAR2SP1n2SB2pw3SPA1c2AB3NFBS3hAR2SP1n2SB2pw3SPA1c2AB3N2BS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS2H32H4S3hAR2SP1n2lo2SB2pw3SPA1c2AB3GEOS3hAR2SP1n2SB2pw3SPA1c2AB3NFB3DNF3MNFS3hAR2SP1n2lo2SB2pw3SPA1c2AB3H12S3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk1H2H1S3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk1H2H1S3hAR2SP1n2SB2pw3SPA1c2AB3SHRS3hAR2SP1n2lo2SB2pw1c2AB3SPL3SHR2H43H12S3hAR2SP1n2lo3CTX2SB2pw3SPA1c2AB3CX13H12S3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H02H8S3hAR2SP1n2SB2pw3SPA1c2AB3DNF3MNFS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS2H32H4S3hAR2SP1n2lo2SB2pw1c2ABS3hAR2SP1n2lo2SB2pw1c2ABS3hAR2SP1n2lo2SB2pw1c2ABS3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR3GEO2H12H32H42H52H82H7S3hAR2SP1n2SB2pw3SPA1c2AB3AB04RZSBS3hAR2SP1n2SB2pw3SPA1c2AB3AB1S3hAR2SP1n2SB2pw3SPA1c2AB3SHR1A1k2Hk2H32H5S3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H02H8S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n2SB2pw3SPA1c2AB2H3S3hAR2SP1n2SB2pw3SPA1c2AB3SHRS3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR3GEO2H12H32H42H52H82H7S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n2SB2pw3SPA1c2AB3AB13N2BSS3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H02H8S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2SB2pw3SPA1c2AB1H2H1S3hAR2SP1n2lo2SB2pw3SPA1c2AB4SPALS3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk2H3S3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk2H3". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK NB FP LOIMG SPL SPH SPA16 T0 T1 CX0 CX1 TC TIDB SB0 SBAL AB0 AB1 ABT ABC ASB TNS CTXNS KF"] Lemma cmsegC1 : ltac2:(CDefT.buildp (gd_tbl_AW_CallocC ()) "Pgp,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq6,(2.&40.)Pq7,(2.&40.)Pq8,(2.&40.)Pq9,(2.&40.)Pq10,(2.&40.)Pq11,(2.&40.)Pb0,(2.&8.)Pshb,(2.&8.)Ppgb,(2.&8.)Pw8,(2.&40.)Pj0,(2.&40.)Pj1,(2.&40.)Pj2,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pid,$5.Pb1,$5.Psj,(4.(2.&8.))Puj,(4.(2.&8.))Pfr0,(4.(2.&8.))Pbs,(4.(2.&40.))P,(7.(1?.=R6.)(26.R6.(27.+2.+1?.)))P,(7.(1?.=R6.)(26.R6.+100.))P,(3?.(8.$5.(2:.&8.R11.)=))P,(2>.(1?.(6.VAB,(36.Vn,))+7???8000.)(1?.+10007???8000.VAB,))P,(40.R;.VT,VCTX,)P,(30.VCS,VT,+1000.)P,(30.VCS,VCTX,+10000.)P,(41.R>.)P,(42.R?.)P,(2<.$11.R10.$43.(13.$1:.(1;.(;.&40.$44.))(16.$1:.)))P,(2<.$11.R11.$45.(13.$1:.(22.(;.&8.+1.))(16.$1:.)))P,(30.VCS,VAB,(36.Vn,))P,(19.$11.R13.VCHB,(13.$1:.(22.R1<.)(13.$1:.(22.(;.&8.R11.))(13.$1:.(39.(;.&40.=))(13.$1:.(3:.(;.&40.(35.Vn,)))(13.$1:.(1;.R19.)(16.$1:.)))))))P,(2<.$11.R14.(6.+7???8000.(46.VAB,+3.))(13.$1:.(22.R1<.)(16.$1:.)))P,(19.$11.R15.VSUB,(13.$1:.(20.(3<.(37.(35.Vn,)+8.))R12.)(16.$1:.)))P,(19.$11.R16.VPGS,(13.$1:.(22.R1=.)(16.$1:.)))P,(19.$11.R17.(6.VT,+:?0.)(13.$1:.(1;.R1<.)(13.$1:.(1;.R1;.)(13.$1:.(1;.R1:.)(16.$1:.)))))P,(1<.$11.R18.(6.VT,+;60.)R12.)P,(8.$1=.(1>.(2.&40.)R13.)#20.)P,(38.R1:.VSPA,R15.=(;.&40.+48470.)(;.&40.Vn,)(;.&40.VSTK,)(;.&40.$=.)(;.&40.+1.)(;.&40.+1.)(;.&40.VSTK,)(;.&40.(6.VSP,-59.))R28.R27.R26.R25.R24.)P,(23.$11.R1;.Vlo,(6.VSPA,-80.))P,(30.VCS,Vlo,(2=.VSP,Vlo,))P,(18.$11.R1=.)(32.$11.VAL,VCS,(47.R3<.R20.R1?.R1=.R27.R1<.R2=.R2<.R2;.R2:.R29.R28.R19.R25.R1>.)(9.(:.(;.&40.+47>40.)(;.&40.(6.VSPA,-80.))R3<.(;.&40.$<.)R3;.R3:.R39.(;.&40.+1.)(;.&40.(35.Vn,))(;.&40.R1=.)R38.R37.R36.R35.R34.R33.R32.(;.&40.VAB,)(;.&40.(36.Vn,))(;.&40.VUB,)(;.&40.VCHB,)(;.&40.$=.)(;.&40.VSTK,)(;.&40.(28.VTID,(27.+2.+20.)))(;.&40.(6.VUB,(35.Vn,)))(;.&40.VT,)(;.&40.+1.)R31.R30.R2?.R2>.)R20.(;.&40.+47>40.)R1?.(?.(2.&40.))R1>.(10.$11.)))")
(* [comment removed for export] *).
    Proof.
      intros gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 t4 t5 t6 q6 q7 q8 q9 q10 q11 b0 shb pgb w8 j0 j1 j2 F fc m id b1 sj uj fr0 bs
        IDB B1B SHB RNG AS TCS CTXCS PS FS GOTFL PPART ACS HDR SHC SH PGC STH STB HL FR ST SCS MI.
      facts. pose proof needed2_primary as [N2E NDB]. pose proof AB_al as ABAL. pose proof (rz_size_bound n) as RZSB.
      assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
      assert (N2B : nfix n + rz_size n <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
        unfold nfix; clear - H H0 NB RZSB; lia. }
      pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MNF.
      assert (RNG' : (AB + needed2 n <= 0x7fff8000) \/ (0x10007fff8000 <= AB /\ AB + needed2 n <= ACEIL)) by (clear - RNG AB1; lia).
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2136 + -56) with (SP + (-137) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_mid AL IMG ALWF CS CSOK ASB) with (W := []) (t3 := x28);
          [ exact NB | exact FP | exact AB0 | exact ABAL | exact RNG' | exact TIDB | exact IDB | exact B1B | exact SHB | exact ACS | exact HDR | exact SHC | exact SH | exact PS
          | exact ST | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI ]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & MI1 & HDR1 & SH1 & ST1)).
      unfold csegC1_post. subst PGS SUB KF CHB UB.
      (* [comment removed for export] *)
      assert (SHR : Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3 = (AB + rz_size n) / 8 + nfix n / 8).
      { rewrite Z.shiftr_div_pow2 by (clear - AB0 RZSB NFB DNF MNF; lia). change (2^3) with 8.
        pose proof (Z.div_mod AB 16 ltac:(lia)) as DA16. pose proof (Z.div_mod (rz_size n) 16 ltac:(lia)) as DR16.
        assert (RZ16 : rz_size n mod 16 = 0) by (unfold rz_size; rewrite Z.mul_comm; apply Z_mod_mult).
        clear - AB0 ABAL RZSB NFB DNF MNF DA16 DR16 RZ16. nia. }
      assert (GEO : 0x65f000 <= AB /\ 16 <= rz_size n /\ rz_size n + nfix n <= needed2 n /\ AB + needed2 n <= ACEIL
                    /\ 0xcbe00 <= (AB + rz_size n) / 8 /\ (AB + rz_size n) / 8 + nfix n / 8 + 1 <= 0x100000000000 /\ 0 <= nfix n / 8 /\ nfix n / 8 * 8 <= nfix n
                    /\ 1 <= Z.min (nfix n) 4096 <= nfix n
                    /\ (AB + rz_size n + nfix n <= 0x7fff8000 \/ 0x10007fff8000 <= AB) /\ lo <= SPA - 512 /\ ACEIL <= lo).
      { clear - AB0 AB1 RNG' RZSB NFB N2B DNF MNF SPAL LOIMG. repeat split; lia. }
      pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E; lia)) as CR. fold c in CR.
      Ltac geo GEO SHR := cbn [disjoint_from cells_size csize Nat.add]; clear - GEO SHR; decompose [and] GEO; repeat split; lia.
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_pg AL IMG ALWF CS CSOK ASB) with (W := []) (pgb := pgb) (x28 := y28);
          [ exact NB | exact FP | exact AB0 | exact ABAL | exact RNG' | exact ACS | | | | | exact ST1 | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI1 ].
        - eapply rw_cells_transport; [exact PGC| exact MU1| exact WM1|]. geo GEO SHR.
        - eapply (poison_statics_transport _ m m1 PS MU1). intros A k Hk. cbn [disjoint_from]. clear - GEO Hk. decompose [and] GEO. repeat split; lia.
        - eapply ro_cells_transport; [exact GOTFL| exact MU1|]. unfold A_GOT_FLAGS. geo GEO SHR.
        - eapply ro_cells_transport; [exact PPART| exact MU1|]. unfold A_FL_PPART. geo GEO SHR. }
      cbn beta. (intros ms2 dd_H; ddestruct dd_H as (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z22 & m2 & -> & MU2 & WM2 & MI2 & PG2 & ST2)).
      assert (MU02 : munch [(lo, SPA + -128); (AB + rz_size n + -16 + 8, AB + rz_size n + -16 + 16); (2147450880 + (AB + rz_size n) / 8, 2147450880 + (AB + rz_size n) / 8 + nfix n / 8);
                            (2147450880 + Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3, 2147450880 + Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3 + 1)] m m2).
      { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM02 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_st AL IMG ALWF CS CSOK) with (W := []);
          [ exact NB | exact FP | | exact CX0 | exact CX1 | exact T0 | exact T1 | exact CTXCS | exact TCS | exact TC | | | exact HL
          | exact ST2 | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI2 | reflexivity ].
        - eapply (allocA_statics_transport _ m m2 T CTX AS MU02). { intros A k Hk. cbn [disjoint_from]. clear - GEO Hk SHR. decompose [and] GEO. repeat split; lia. }
          cbn [disjoint_from]. clear - GEO SHR CX1 CTXNS ABC. decompose [and] GEO. repeat split; lia.
        - eapply rw_cells_transport; [exact STH| exact MU02| exact WM02|]. cbn [disjoint_from cells_size csize Nat.add]. clear - GEO SHR T1 TNS ABT. decompose [and] GEO. repeat split; lia.
        - eapply u64arr_transport; [exact STB| exact MU02| exact WM02|]. rewrite HL. cbn [disjoint_from]. clear - GEO SHR T1 TNS ABT. decompose [and] GEO. repeat split; lia. }
      cbn beta. (intros ms3 dd_H; ddestruct dd_H as (u1 & u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & k0 & k1 & k2 & bs' & m3 & -> & MU3 & WM3 & MI3 & STH3 & STB3 & HL3 & ST3)).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_fill AL IMG ALWF CS CSOK) with (W := []) (uj := uj) (fill := 0);
          [ exact NB | exact AB0 | exact AB1 | clear; lia | exact ACS | | | | exact ST3 | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | exact MI3 ].
        - intros NE0. exfalso. apply NE0. reflexivity.
        - eapply (fin_statics_transport _ m2 m3); [| exact MU3| intros A k Hk; cbn [disjoint_from]; clear - GEO Hk T0; decompose [and] GEO; repeat split; lia].
          eapply (fin_statics_transport _ m m2 FS MU02). intros A k Hk; cbn [disjoint_from]; clear - GEO Hk SHR; decompose [and] GEO; repeat split; lia.
        - unfold allocA_frame in *. eapply rw_cells_transport; [| exact MU3| exact WM3|].
          { eapply rw_cells_transport; [exact FR| exact MU02| exact WM02|]. cbn [disjoint_from cells_size csize Nat.add]. clear - GEO SHR SPL. subst SPA. decompose [and] GEO. repeat split; lia. }
          cbn [disjoint_from cells_size csize Nat.add]. clear - GEO T1 ABT CR. subst SPA. decompose [and] GEO. repeat split; lia. }
      cbn beta. (intros ms4 dd_H; ddestruct dd_H as (v1 & v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & w28 & w29 & w30 & w31 & m4 & -> & MU4' & WM4 & MI4 & _ & NOF & ST4)).
      destruct (NOF eq_refl) as (EM4 & _). subst m4.
      assert (MU4 : munch [(lo, SPA + -128)] m3 m3) by (apply munch_refl). clear MU4'.
      (* [comment removed for export] *)
      apply evtA_done. deexists 17. dexists k0, k1, k2, bs'. exists m3. split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU02]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_trans. { eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
      split; [eapply wmono_trans; [exact WM02| eapply wmono_trans; [exact WM3| exact WM4]]|]. split; [exact MI4|].
      assert (MU24 : munch [(lo, SPA + -128); (T + 2800, T + 3168)] m2 m3).
      { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM24 : wmono asegs m2 m3) by (eapply wmono_trans; [exact WM3| exact WM4]).
      assert (MU14 : munch [(lo, SPA + -128); (2147450880 + Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3, 2147450880 + Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3 + 1);
                            (T + 2800, T + 3168)] m1 m3).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
        eapply munch_weaken; [| exact MU24]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM14 : wmono asegs m1 m3) by (eapply wmono_trans; [exact WM2| exact WM24]).
      split. { unfold allocA_frame in *. eapply rw_cells_transport; [| exact MU24| exact WM24|].
               { eapply rw_cells_transport; [exact FR| exact MU02| exact WM02|]. cbn [disjoint_from cells_size csize Nat.add]. clear - GEO SHR SPL. subst SPA. decompose [and] GEO. repeat split; lia. }
               cbn [disjoint_from cells_size csize Nat.add]. clear - GEO T1 ABT CR SPL. subst SPA. decompose [and] GEO. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact HDR1| exact MU14| exact WM14|]. cbn [disjoint_from cells_size csize Nat.add]. clear - GEO SHR T1 ABT. decompose [and] GEO. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact SH1| exact MU14| exact WM14|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; lia).
               clear - GEO SHR T1 TNS ABT. decompose [and] GEO. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact PG2| exact MU24| exact WM24|]. cbn [disjoint_from cells_size csize Nat.add].
               clear - GEO SHR T1 TNS ABT. decompose [and] GEO. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact STH3| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add]. clear - GEO T1 ABT. decompose [and] GEO. repeat split; lia. }
      split. { eapply u64arr_transport; [exact STB3| exact MU4| exact WM4|]. rewrite HL3. cbn [disjoint_from]. clear - GEO T1 ABT. decompose [and] GEO. repeat split; lia. }
      split; [exact HL3|]. exact ST4.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition csegC2_post (ra gp : word) (F : bvmap 5 word) (fc : bv 32) (id : Z) (b1 : Z)
        (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocC ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(7.(8.$0.R10.(9.(:.O13.(;.&40.VSP,)O12.(;.&40.$<.)R?.R>.R=.O=.O<.(;.&40.VUB,)R<.R;.R:.R9.R8.R7.R6.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.R5.R4.R3.R2.)O11.(48.O13.)O10.(?.(2.&40.))R1.(10.$11.)))(7.(12.(13.(14.$5.$5.)(15.$5.$5.Vlo,VSP,)(13.(14.$5.$5.)(15.$5.$5.VCHB,(6.VCHB,+2.))(13.(14.$5.$5.)(15.$5.$5.VAB,(6.VAB,+10.))(13.(14.$5.$5.)(15.$5.$5.VUB,(6.VUB,Vn,))(16.(14.$5.$5.))))))O1.R1.)(7.(17.$11.O1.R1.)(7.(18.$11.R1.)(7.(19.$11.R1.VCHB,(13.$1:.(22.(;.&8.$49.))(13.$1:.(22.(;.&8.(4:.O>.+?3.)))(13.$1:.(39.(;.&40.=))(13.$1:.(3:.(;.&40.(35.Vn,)))(13.$1:.(1;.(;.&40.(3;.(28.VTID,(27.+2.+20.))O?.)))(16.$1:.)))))))(7.P,(26.+10.(4;.Vn,))(19.$11.R2.VAB,(13.$1:.(1;.(;.&40.$4<.))(13.$1:.(1;.(;.&40.VCHB,))(16.$1:.))))(7.(19.$11.R1.VUB,(13.$1:.(20.(3<.Vn,)(3=.(2.&8.)(;.&8.=)(3<.Vn,)))(16.$1:.)))(23.$11.R1.Vlo,VSP,)))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@L10029979475.3  L11369523398.2  L11380347005.3  L11741316847.7  L12589220470.15 L12589220599.18 L14397645527.7  L14883623720.3  L15036699472.187L18488770533.15 L19232423412.16 L20070261741.3  L21108182031.18 L21108182031.19 L21108182158.15 L21175256044.3  L21590808327.15 L23464131942.157L23663032997.15 L24184345536.19 L2424857170.2   L24888640626.2  L25307436372.157L26193403755.3  L26275543149.2  L27697017043.3  L27705282402.5  L27848808849.2  L27991817377.3  L29105961052.3  L29355480427.3  L31659743062.2  L31747570154.0  L32108121837.3  L33719216517.6  L34119949365.3  L36193165570.2  L36571201320.0  L38124983873.12 L38235734261.1  L39046678806.2  L4004494035.3   L40074140174.0  L40156106605.2  L40480480168.3  L41466795432.3  L42333736318.16 L4337221374.16  L44986836149.3  L46148810195.3  L46367748204.183L47648045779.3  L48063988754.3  L48992174697.181L49002707826.183L49858401057.0  L49871936565.3  L49890578593.3  L51170281315.15 L51170281442.18 L51170281442.19 L51939338803.3  L5423397493.2   L54702911965.191L60989450125.15 L61030858054.155L61653547298.189L6178129507.19  L62312151187.14 L62883354484.8  L63374621462.156L63988471514.193L67834316406.3  L67995507890.1  L6812711733.3   L7920407119.181 L8797080822.4   L9004691366.15  L9717231777.0   00000;00?00J00\01E02102H02S03N04804O04Z05O06@06i07407F08908c09O09U09Y0:L0:S0:[0:f0:n0;50;@0;K0;R0;V0;W0;b0<50<<0<?0<@0<c0<g0<o0=:0=;0=C0=N0=Y0>90>g0>n0?90@00@;0@F0A=0B40B50B<0BG0Bk0Ce0D[0Db0Dj0Ee0F>0G90H40He0IF0Ib0J]0KX0K`0Kd0Kk0Lb0Lm0MK0MLS2SP2lo3SPLS2SPS2SP2lo3SPLS1n2SB2pw1c2AB3N2BS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG1A1k2H1S3hAR2SP1n2lo2SB2pw3SPA1c2AB4RZSB3NFB1A1k2H1S1n2SB2pw1c2AB3AB04RZSBS2SP2lo3SPLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n2lo2SB2pw1c2AB5LOIMG3AB13NFB3N2BS3hAR1n2SB2pw1c2AB4RZSBS2SP2lo3SPLS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB13NFB3N2B1A1k2H2S3hAR2SP1n2lo2SB2pw3STK1c2AB5LOIMG3AB13N2B1A1k2H2S3hAR2SP1n2SB2pw3SPA1c2AB3AB04RZSB1A1k2H1S2SP2lo3SPLS3hAR1n2SB2pw1c2ABS3hAR2SP1n1T2SB2pw1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB13N2BS3hAR2SP1n2lo2SB2pw3STK1c2AB4RZSB3NFB1A1k2H1S1n2NBS2SPS3hAR2SP1n1T2SB2pw1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SP2loS2SP3SPHS1n3N2E3NDBS1n1H2H0S2SP2loS2SP2lo3SPLS2SP2lo3SPLS2SP2loS2SPSS2SP2lo3SPLS1n2SB2pw1c2AB4RZSBS2SP2loS1nSS3hAR1n2lo2SB2pw1c2AB5LOIMG3AB13N2BS2loS2SB3SB1S2SP2lo3SPLSS2SP3SPHS2SP2lo3SPLS2SP2lo3SPLS2SP1n2lo2SB2pw1c2AB2UB3CHB1x2HxS3hAR2SP1n2lo2SB2pw1c2AB5LOIMG3AB13NFB3N2B3HRZS2SP2loS2SP2lo3SPLS3hAR2SP1n1T2SB2pw3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SP2lo3SPLS2SP2lo3SPLS3hAR2SP1n1T2SB2pw3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n1T2SB2pw3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLSS2SP2loS2SP2lo3SPLS3hAR2SP1n2SB2pw3SPA1c2AB3AB01A1k2H1S3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB14RZSB3NFB3N2B1A1k2H2S3hAR2SP1n2lo2SB2pw3STK1c2AB5LOIMG3AB14RZSB3N2B1A1k2H2S2SP2loS2SP3SPHS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n2SB2pw3SPA1c2ABS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n2lo2SB2pw3STK1c2AB5LOIMG3AB13N2B1A1k2H2S3hAR1n2SB2pw1c2AB2NB3AB13NFB3N2BS1n2SB2pw1c2AB3UBH4RZSB4ABSBS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS1A1k2HkS2SPS2SP2loS3hAR2SP1n1T2SB2pw3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SP2lo3STKS3hAR2SP1n2SB2pw3SPA1c2AB4RZSBS". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK NB FP LOIMG SPL SPH SPA16 SB0 SB1 SBAL AB0 AB1 SUB PGS KF"] Lemma cmsegC2 : ltac2:(CDefT.buildp (gd_tbl_AW_CallocC ()) "Pra,(2.&40.)Pgp,(2.&40.)Px1,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px22,(2.&40.)Px28,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pq0,(2.&40.)Pq1,(2.&40.)Pq2,(2.&40.)Pq3,(2.&40.)Pq4,(2.&40.)Pq5,(2.&40.)Pq6,(2.&40.)Pq7,(2.&40.)Pq8,(2.&40.)Pq9,(2.&40.)Pq10,(2.&40.)Pq11,(2.&40.)Pp0,(2.&40.)Pp1,(2.&40.)Pp2,(2.&40.)Pp3,(2.&40.)Pmg0,(2.&40.)Pmg1,(2.&40.)Pb0,(2.&8.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pid,$5.Pb1,$5.Psize,$5.Pfr0,(4.(2.&8.))Pfr1,(4.(2.&8.))Pfr2,(4.(2.&8.))Pfr3,(4.(2.&8.))Pfr4,(4.(2.&8.))Puj,(4.(2.&8.))Pws,(4.(2.&40.))P,(7.(1?.=R9.)(26.R9.+100.))P,(26.VUB,(6.VSB,(27.+2.+25.)))P,(30.VCS,VAB,(36.Vn,))P,(42.R>.)P,(2<.$11.R?.(6.$=.+20.)(13.$1:.(1;.(;.&40.VSB,))(16.$1:.)))P,(19.$11.R10.VCHB,(13.$1:.(22.R13.)(13.$1:.(22.(;.&8.R>.))(13.$1:.(39.(;.&40.=))(13.$1:.(3:.(;.&40.(35.Vn,)))(13.$1:.(1;.(;.&40.(3;.(28.VTID,(27.+2.+20.))R?.)))(16.$1:.)))))))P,P,(26.+10.(4;.Vn,))(19.$11.R12.VAB,(13.$1:.(1;.R17.)(13.$1:.(1;.R16.)(16.$1:.))))P,(19.$11.R12.VUB,(13.$1:.(20.(3<.Vn,)R9.)(16.$1:.)))P,(38.R13.VSPA,R?.=(;.&40.+48470.)(;.&40.Vn,)(;.&40.VSTK,)(;.&40.$=.)(;.&40.+1.)(;.&40.+1.)(;.&40.VSTK,)(;.&40.(6.VSP,-59.))R21.R20.R1?.R1>.R1=.)P,(19.$11.R14.(6.VSTK,-38.)(13.$1:.(20.#8.R<.)(13.$1:.(1;.R1:.)(13.$1:.(1;.R1;.)(13.$1:.(1;.R1<.)(13.$1:.(1;.R1=.)(13.$1:.(1;.(;.&40.+699<4.))(16.$1:.))))))))P,(19.$11.R15.(6.VSP,-40.)(13.$1:.(1;.R24.)(13.$1:.(1;.R25.)(13.$1:.(1;.R26.)(13.$1:.(1;.R27.)(13.$1:.(1;.R28.)(13.$1:.(1;.R29.)(13.$1:.(1;.R2:.)(13.$1:.(1;.R3=.)(16.$1:.))))))))))P,(19.$11.R16.(6.VSTK,-8.)(13.$1:.(20.#8.R?.)(16.$1:.)))P,(19.$11.R17.VSTK,(13.$1:.(1;.(;.&40.(6.VSTK,+10.)))(13.$1:.(1;.(;.&40.R14.))(16.$1:.))))P,(1<.$11.R18.(6.VSTK,+10.)R>.)P,(8.$1=.(1>.(2.&40.)R?.)#1>.)P,(19.$11.R1:.(6.VSTK,+100.)(13.$1:.(20.#708.R15.)(16.$1:.)))P,(19.$11.R1;.(6.VSTK,+808.)(13.$1:.(1;.(;.&40.VSP,))(16.$1:.)))P,(19.$11.R1<.(6.VSTK,+810.)(13.$1:.(20.#8.R16.)(16.$1:.)))P,(23.$11.R1=.Vlo,(6.VSPA,-80.))P,(30.VCS,Vlo,(2=.VSP,Vlo,))P,(18.$11.R1?.)(32.$11.VAL,VCS,(4=.R48.R47.R22.R21.R1?.R1>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R20.)(9.(:.R46.(;.&40.(6.VSPA,-80.))R47.(;.&40.$<.)R45.R44.R43.(;.&40.+1.)(;.&40.(35.Vn,))R42.R41.R40.R3?.R3>.R3=.R3<.R3;.(;.&40.VAB,)(;.&40.(36.Vn,))(;.&40.VUB,)(;.&40.VCHB,)R3:.(;.&40.VSTK,)(;.&40.(28.VTID,(27.+2.+20.)))(;.&40.(6.VUB,(35.Vn,)))(;.&40.VT,)(;.&40.+1.)R39.R38.R37.R36.)R22.(;.&40.+48174.)R21.(?.(2.&40.))R20.(10.$11.)))")
(* [comment removed for export] *).
    Proof.
      intros ra gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 t4 t5 t6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 p0 p1 p2 p3 mg0 mg1 b0 F fc m id b1 size fr0 fr1 fr2 fr3 fr4 uj ws
        B1B UBH ACS FS SBC HDR MG UC FR AFR FR8 FJ STKC HTR HL F1800 TFB F8 ST SCS MI.
      facts. pose proof needed2_primary as [N2E NDB]. pose proof AB_al as ABAL. pose proof (rz_size_bound n) as RZSB.
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2136 + -56) with (SP + (-137) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      unfold csegC2_post.
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_fin2 AL IMG ALWF CS CSOK) with (W := []) (mg0 := mg0) (mg1 := mg1);
          [ exact NB | exact AB0 | exact ABAL | exact AB1 | exact B1B | exact ACS | exact HDR | exact MG | exact FS | exact FR
          | exact ST | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI | reflexivity ]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & MI1 & HDR1 & MG1 & ST1)).
      replace (ret_pc (Z_to_bv 64 0x48470)) with (Z_to_bv 64 0x48470) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      fold UB in HDR1 |- *. fold CHB in MU1, HDR1, MG1 |- *.
      assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
      assert (N2B : nfix n + rz_size n <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
        unfold nfix; clear - H H0 NB RZSB; lia. }
      assert (DJ1 : forall A k, (A + k <= lo \/ SPA <= A) -> lo <= A -> disjoint_from [(lo, SPA); (CHB, CHB + 2); (AB, AB + 16)] A k).
      { intros A k H1 H2. cbn [disjoint_from]. subst CHB UB. clear - H1 H2 AB1 LOIMG RZSB NFB N2B. repeat split; lia. }
      assert (DJI : forall A k, A + k <= 0x65f000 -> disjoint_from [(lo, SPA); (CHB, CHB + 2); (AB, AB + 16)] A k).
      { intros A k H1. cbn [disjoint_from]. subst CHB UB. clear - H1 AB0 LOIMG RZSB. repeat split; lia. }
      assert (ABSB : SB <= AB) by (subst AB; pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^32) ltac:(clear; lia)); pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E; lia)); subst c; clear - H H0; nia).
      (* [comment removed for export] *)
      replace (Z_to_bv 64 SPA) with (Z_to_bv 64 (STK + -8 + -48)) by (subst SPA STK; f_equal; lia).
      eapply evtA_cut.
      { eapply (acalloc_ok_prim AL IMG ALWF CS CSOK) with (SP := STK + -8) (W := []) (m0 := m1) (junk := uj);
          [ | clear - NB; lia | | exact SB0 | clear - SB1; lia | | | | | | | | | exact LOIMG | subst STK; clear - SPL; lia | subst STK; clear - SPH; lia | | | apply munch_refl | apply wmono_refl | exact MI1 ].
        - subst UB. clear - AB0 RZSB. lia.
        - subst UB. clear - AB0 AB1 RZSB NDB N2E NFB N2B NB. lia.
        - subst UB. clear - ABSB UBH RZSB. lia.
        - eapply ro_cells_transport; [exact SBC| exact MU1| apply DJI; unfold A_INSTANCE; cbn; clear; lia].
        - eapply (fin_statics_transport _ m m1 FS MU1). intros A k Hk. apply DJI; clear - Hk; lia.
        - eapply rw_cells_transport; [exact UC| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - NB; lia). subst CHB UB. clear - AB1 LOIMG RZSB NFB N2B NB. unfold nfix in *. repeat split; lia.
        - subst UB. eapply (crange_sub CS AB (needed2 n)); [exact ACS| clear - RZSB; lia| clear - N2B NFB; unfold nfix in *; lia].
        - subst UB. clear - AB1 LOIMG N2B NFB RZSB. unfold nfix in *. lia.
        - replace (STK + -8 + -48) with SPA by (subst STK SPA; lia). eapply rw_cells_transport; [exact AFR| exact MU1| exact WM1| apply DJ1; cbn; subst SPA STK; clear - SPL; lia].
        - replace (STK + -8 + -48) with SPA by (subst STK SPA; lia). exact ST1.
        - subst STK. clear - SPA16. replace (SP + -2136 + -8) with (SP + (-134) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16.
        - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst STK; clear; lia]. }
      cbn beta. (intros ms2 dd_H; ddestruct dd_H as (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m2 & -> & MU2 & WM2 & MI2 & ZR & ST2)).
      replace (ret_pc (Z_to_bv 64 0x699c4)) with (Z_to_bv 64 0x699c4) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      assert (MU02 : munch [(lo, STK + -8); (CHB, CHB + 2); (AB, AB + 16); (UB, UB + n)] m m2).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. subst STK SPA. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
        eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
      assert (WM02 : wmono asegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
      assert (DJ2 : forall A k, (A + k <= lo \/ STK + -8 <= A) -> lo <= A -> disjoint_from [(lo, STK + -8); (CHB, CHB + 2); (AB, AB + 16); (UB, UB + n)] A k).
      { intros A k H1 H2. cbn [disjoint_from]. subst CHB UB. clear - H1 H2 AB1 LOIMG RZSB NFB N2B NB. unfold nfix in *. repeat split; lia. }
      (* [comment removed for export] *)
      assert (ST3 : stk asegs m2 lo (SP + -64)).
      { replace (STK + -8) with (SP + -2144) in ST2 by (subst STK; lia).
        assert (FJ1 : rw_cells asegs m2 (SP + -2144) [CB 8 fr3]).
        { replace (SP + -2144) with (STK + -8) by (subst STK; lia). eapply rw_cells_transport; [exact FJ| exact MU02| exact WM02| apply DJ2; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m2 lo (SP + -2144) _ ST2 FJ1 ltac:(clear - SPL; lia)) as R. cbn [cells_size csize Nat.add] in R.
        replace (SP + -2144 + Z.of_nat 8) with STK in R by (subst STK; lia).
        assert (STKC1 : rw_cells asegs m2 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)])
          by (eapply rw_cells_transport; [exact STKC| exact MU02| exact WM02| apply DJ2; cbn; subst STK SPA; clear - SPL; lia]).
        pose proof (stk_release asegs m2 lo STK _ R STKC1 ltac:(subst STK; clear - SPL; lia)) as R0. cbn [cells_size csize Nat.add] in R0.
        assert (HTR1 : u64arr asegs m2 (STK + 16) ws)
          by (eapply u64arr_transport; [exact HTR| exact MU02| exact WM02| apply DJ2; rewrite ?HL; cbn; subst STK SPA; clear - SPL; lia]).
        assert (TRC : rw_cells asegs m2 (STK + Z.of_nat 16) [CB (length (u64s ws)) (u64s ws)]).
        { replace (STK + Z.of_nat 16) with (STK + 16) by lia. apply rw_cells_of_u8arr. destruct HTR1 as [HB HW]. split; [exact HB|]. rewrite u64s_length, HL. rewrite HL in HW. replace (Z.of_nat (8 * 30)) with (8 * Z.of_nat 30) by (clear; lia). exact HW. }
        pose proof (stk_release asegs m2 lo _ _ R0 TRC ltac:(subst STK; clear - SPL; lia)) as R1. cbn [cells_size csize Nat.add] in R1. rewrite u64s_length, HL in R1.
        assert (F1800' : rw_cells asegs m2 (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) [CB 1800 fr1]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) with (STK + 256) by lia.
          eapply rw_cells_transport; [exact F1800| exact MU02| exact WM02| apply DJ2; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m2 lo _ _ R1 F1800' ltac:(subst STK; clear - SPL; lia)) as R2. cbn [cells_size csize Nat.add] in R2.
        assert (TFB' : rw_cells asegs m2 (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) [C8 (Z_to_bv 64 SP)]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) with (STK + 2056) by lia.
          eapply rw_cells_transport; [exact TFB| exact MU02| exact WM02| apply DJ2; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m2 lo _ _ R2 TFB' ltac:(subst STK; clear - SPL; lia)) as R3. cbn [cells_size csize Nat.add] in R3.
        assert (F8' : rw_cells asegs m2 (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) [CB 8 fr2]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) with (STK + 2064) by lia.
          eapply rw_cells_transport; [exact F8| exact MU02| exact WM02| apply DJ2; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m2 lo _ _ R3 F8' ltac:(subst STK; clear - SPL; lia)) as R4. cbn [cells_size csize Nat.add] in R4.
        lazymatch type of R4 with stk _ _ _ ?hi => replace hi with (SP + -64) in R4 by (subst STK; clear; lia) end. exact R4. }
      assert (FR8' : rw_cells asegs m2 (SP + -64) [C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra])
        by (eapply rw_cells_transport; [exact FR8| exact MU02| exact WM02| apply DJ2; cbn; subst SPA; clear - SPL; lia]).
      (* [comment removed for export] *)
      eapply evtA_mono.
      { replace (STK + -8) with (SP + -2144) by (subst STK; lia). eapply (calloc_epi AL IMG ALWF CS CSOK); [exact FR8'| exact ST3| exact LOIMG| clear - SPL; lia| clear - SPH; lia| exact SPA16| exact SCS| exact MI2]. }
      cbn beta. intros ms3 (-> & ST4).
      deexists 14. exists m2. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU02]. unfold sub_fp; cbn [outside]. subst STK. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
      split; [exact WM02|]. split; [exact MI2|].
      split. { eapply rw_cells_transport; [exact HDR1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB UB STK. clear - AB1 LOIMG SPL RZSB NFB N2B NB. repeat split; lia. }
      split. { intros HRZ. eapply rw_cells_transport; [exact (MG1 HRZ)| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB UB STK. clear - AB1 LOIMG SPL RZSB HRZ NFB N2B NB. repeat split; lia. }
      split; [exact ZR| exact ST4].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End SegB.

End CallocC.

End ARUN_1.
