(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_MallocA AW_DepotA AW_DepotB AW_Poison AKinv AKinvS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemset AW_IAInit AW_Dealloc AW_FreeA AW_QPut AW_Enqueue AW_Drain AW_FreeC AW_FreeTop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
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
Ltac2 gd_tbl_AW_FreeSegs () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_QPUT_RA1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_ENQUEUE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.put_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_PC_FREE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeA.A_FREE_RA2"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeTop.free_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.FreeSegs.fsegP0_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_QC_RA1"; "ARUN_1.FreeSegs.fsegPA_W"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.qc_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.batch_hdr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.app"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Peano.lt"; "ARUN_1.FreeSegs.fsegPA_post"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.pc24_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SPACEBEG_CELL"; "ARUN_1.FreeSegs.fsegPH_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].

Section ARUN_1. Context {hAR : arun}.
Section FreeSegs.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Definition fsegP0_post (SP : Z) (gp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (p n lo T CTX : Z) (mC : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))ZSTK,$4.(5.O10.-850.)ZS,$4.(5.+7???8000.(6.O6.+8.))Zk,$4.(6.(5.O5.+7.)+8.)(7.(8.$0.R?.(9.(:.(;.&40.$<.)(;.&40.(5.R3.-50.))O?.(;.&40.$=.)R>.R=.R<.(;.&40.(5.$>.+2=8.))(;.&40.(5.O3.+50.))(;.&40.(5.O3.+50.))(;.&40.(5.O3.+=0.))(;.&40.R3.)(;.&40.(5.O6.-10.))(;.&40.O5.)R;.R:.R9.(;.&40.O5.)(;.&40.R3.)(;.&40.(5.O3.+=0.))(;.&40.(5.O6.-10.))(;.&40.$?.)O=.O<.O;.O:.O9.R8.R7.R6.R5.)O8.(;.&40.$10.)O7.(11.(2.&40.))R4.(12.$13.)))(7.(14.(15.(16.$4.$4.)(17.$4.$4.O4.R3.)(15.(16.$4.$4.)(17.$4.$4.O6.(5.O6.+8.))(15.(16.$4.$4.)(17.$4.$4.R2.(5.R2.R1.))(18.(16.$4.$4.)))))O1.R4.)(7.(19.$13.O1.R4.)(7.(1:.$13.R4.)(7.(1;.R4.R3.O3.R3.O>.(;.&40.(5.O10.-51.))(;.&40.R3.)(;.&40.+1.)(;.&40.$1<.)(;.&40.O6.)(;.&40.O10.)(;.&40.$1=.))(7.(1>.$13.R4.R2.(15.$1?.(20.(21.R1.)(22.(2.&8.)(;.&8.+?=.)(21.R1.)))(18.$1?.)))(7.(23.$13.R4.O6.+8.)(7.(24.R4.O3.O2.)(25.$13.R4.O4.(5.R3.-50.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01E0?L11022268302.17L12137473770.6 L12137652708.2 L12297272267.21L15515971117.8 L17120848823.0 L18186806754.7 L18188774632.7 L18188856552.3 L18188889062.3 L18188948954.2 L19167748205.8 L21049500170.6 L22406284478.4 L25426245911.7 L25426245911.9 L25432523821.10L26870639355.8 L26880640045.2 L27846297964.3 L29949905540.9 L31735977102.21L35787266409.5 L35787266409.8 L35787266413.5 L35788968035.10L35788968035.8 L35789379437.5 L35789449426.7 L35789449553.6 L36644218784.6 L36644267936.2 L36644364462.3 L36949723459.4 L36967530425.11L38237949960.3 L39332637397.0 L40938924652.1 L42627424012.7 L42627473164.3 L42627504130.3 L42629649926.6 L43865612567.8 L43867762451.3 L43867820204.5 L43867820335.4 L43868104733.6 L43868104733.8 L46532565131.2 L51794544653.3 L56786826630.8 L57628699659.6 L58805140480.17L61045092046.21L61123023741.10L61536368211.4 L61538482263.6 L61745276307.4 L61745276311.4 L61745276311.7 L61746982045.8 L61747063965.5 L61747424147.4 L61747483692.6 L61747484079.5 L62391680077.21L63995254982.8 L64146542324.21L64181499405.21L65337180824.11L66552202845.8 L66552284765.4 L66552381779.4 L66554433367.6 L66774298937.3 L67172332582.3 L67172381734.7 L67172748439.3 L67172748564.2 L67172823848.3 L67174874412.7 L9265737838.6  L9267362148.3  L9267444068.7  L9267789418.3  00000V00g00h01e02902:02;02<02=02>02D02X02d02o03B03Z04804H04I04P04g05B05C05D05E05F05Z05[05\05]05^05d05e05j06>06B06C06F06G06H06I06U06V06W06X06Y06Z06o07507=07@07P08A08\09109209A09B09C09D09X09Y09Z09[09\0:50:80:N0:g0;?0;@0;A0;B0;Q0;R0;S0;T0;^0;_0;`0;a0<:0<;0<<0<=S3hAR2SP1p1n2lo1T1k3THI2T15LOIMG2KB2SRS3hAR1p1n1k2PH2KBFS3hAR2SP1p1n2lo1T3CTX1k2PL3RNG2T02T13CX13APT3APC5LOIMG3SPL2KBS2SP1p1n2lo1k3APS2KBSFFFFS1T2T0S2SP1p1n2lo1k3APS2KBS3hAR1p1k2PHS1n2NB1H2H0S2SP1p2lo1A1j2H12H2S2SP1p2lo1k2SR1A1j2H12H2S3hAR2SP1p2lo1k5LOIMG2SR1A1j1HS3hAR1p2PL1A1j1HFS2SP2loS3hAR2SP2lo5LOIMG1A1j1HS3hAR1p1n1T3CTX1k2T03APC2KBFFFFS2SP1p1n2lo1k3APS2KBFFFFS1n2NBFS1p1kS3hAR1p1k2PL2PH1H2H0S2loSS1pFFFS3hAR2SP3SPHFFFFFS3hAR1p1n1k3RNG2HK2KBS1p2PLS1n1k2KBS1pS2SP1p2lo1k1y2HyS3hAR2SP1p1n2lo1T3CTX1k3THI3CX15CTXNS5LOIMG2KB2SRS3hAR1p1n1T3CTX1k2T03APC2KBS3hAR1p1n1k2PH3RNG2KBFS3hAR2SP2lo3SPLFFFS2SP1p1n2lo1k3APS2KBFFFFS3hAR2SP2lo3CTX3CX15LOIMGS1pS3hAR2SP2lo1T2T15LOIMGS3hAR2SP2lo3CTX3CX15LOIMGS3hAR2SP1p2lo1k2PH5LOIMGFFFS3hAR2SP2lo3SPLFFFS3hAR1T2T1FFFS3hAR2SP2lo5LOIMG3SPL3SPHFFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma fsegP0 : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "Pgp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pidw,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$4.Pp,$4.Pb1,$4.Pn,$4.Pctx,$4.Plo,$4.PT,$4.PCTX,$4.Pjunk,(26.(2.&8.))PF,(27.&5.(2.&40.))Pfc,(2.&20.)PmC,P,(2.&40.)(3.(2.&8.))ZSTK,$4.(5.R<.-850.)Zk,$4.(6.(5.R:.+7.)+8.)P,(28.(5.+65?000.+10.)R=.)P,(28.(5.R>.(29.+8.R2.))(2:.VhAR,))P,(8.$4.(2;.R?.+10.)=)P,(7.(28.=R>.)(28.R>.(2<.+2.+1<.)))P,(2=.(7.(28.(5.R11.+8.)+7???8000.)(28.(5.R11.(29.+8.R5.))+7???8000.))(7.(28.+10007???8008.R11.)(28.(5.R11.+8.)(2<.+2.+2?.))))P,(7.(7.(28.+1000.R=.)(2=.(28.(5.R=.+1000.)+10000.)(28.+65?000.R=.)))(2=.(28.(5.R=.+1000.)+7???7000.)(28.+10007???8000.R=.)))P,(7.(28.+1000.R>.)(2=.(28.(5.R>.+1000.)+10000.)(28.+65?000.R>.)))P,(28.(5.R?.+1000.)(2:.VhAR,))P,(28.+65?000.R?.)P,(28.(5.R10.+10000.)(2:.VhAR,))P,(1>.$13.R=.(5.R17.-10.)(2>.R16.+3.))P,(1>.$13.R>.(5.R18.-<.)(2?.R16.R15.))P,(23.$13.R?.R19.+8.)P,(30.VCS,(5.R1:.-10.)(5.+10.(29.+8.(31.R>.+1.))))P,(1>.$13.R11.(5.+7???8000.(6.R1;.+8.))(15.$1?.(20.(21.R?.)R14.)(18.$1?.)))P,(1>.$13.R12.(5.R11.-30.)(15.$1?.(32.(;.&40.R11.))(15.$1?.(32.(;.&40.+1.))(15.$1?.(32.(;.&40.$1<.))(15.$1?.(32.(;.&40.R1<.))(15.$1?.(32.(;.&40.R1=.))(15.$1?.(32.(;.&40.$1=.))(18.$1?.))))))))P,(24.R13.R18.R17.)P,(30.VCS,R19.+1000.)P,(2=.(28.(5.R1:.+1000.)(33.R1?.+10.))(28.(5.R1?.(29.+8.(31.R13.+1.)))R1:.))P,(2=.(28.(5.R1:.+10000.)(33.R20.+10.))(28.(5.R20.+8.)R1:.))P,(2=.(28.R22.R1;.)(28.(5.R1;.+10000.)R1=.))P,(2=.(28.(5.R1<.+10000.)+7???8000.)(28.+10007???8000.R1<.))P,(2=.(28.R24.(33.R23.+10.))(28.(5.R23.(29.+8.(31.R17.+1.)))R1?.))P,(2=.(28.R25.R1?.)(28.(5.R1?.+1000.)R20.))P,(25.$13.R1;.R21.(5.R1:.-30.))P,(28.(2:.VhAR,)R22.)P,(28.R23.(33.R28.+1000.))P,(28.R29.(2<.+2.+3>.))P,(8.$4.(2;.R2:.+10.)=)P,(30.VCS,R26.(33.R2;.R26.))P,(1:.$13.R21.)(34.$13.VAL,VCS,(35.R2=.R43.R37.R36.R35.R34.R33.R32.R24.R23.R2<.R2:.R28.R27.R26.R22.)(9.(:.(;.&40.$36.)(;.&40.(5.R21.-30.))R43.(;.&40.$=.)R42.R41.R40.(;.&40.(5.R2<.-10.))(;.&40.R21.)R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.(;.&40.$>.)(;.&40.=)(;.&40.R27.)(;.&40.(5.R2=.-51.))R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)R24.(;.&40.$36.)R23.(11.(2.&40.))R22.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros gp t0 t1 t2 idw a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx lo T CTX junk F fc mC STK k
      PL PH PA NB RNG THI T0 T1 CX0 CX1 HW0 HW1 WR PCS SH QFR FST TCS APT APC ASC CTXNS APS AST ST LOIMG SPL SPH SPA SCS MI.
    assert (HK : k = (n + 7) / 8) by reflexivity. clearbody k. subst STK.
    assert (KB : 0 <= k /\ 8 * k < n + 8 + 8) by (rewrite HK; pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)); clear -H H0 NB; lia).
    dpose FST as (MS8 & MF & TT & C8' & QM & GF & FL & PS).
    assert (STAL : (SP + -2128) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, SPA; reflexivity).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (qc_B AL IMG ALWF CS CSOK) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (lo := lo) (STK := SP + -2128) (m0 := mC);
        first [exact HW0 | exact HW1 | exact WR | exact QFR | exact ST | exact LOIMG | exact MI | apply munch_refl | apply wmono_refl
              | eapply crange_sub; [exact PCS| clear; lia| clear -KB; lia]
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -PL; lia | clear -PH KB; lia | clear -NB; lia | clear -SPL LOIMG SPH; lia | clear -T0; lia | clear -T1; lia | clear -SPL; lia | clear -SPH; lia
              | clear -APS SPL KB; lia ]. }
    cbv beta. (intros ms1 dd_H; ddestruct dd_H as (y16 & y17 & m1 & -> & MU1 & WM1 & MI1 & WR1 & ST1)).
    assert (DJ1 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= p \/ p + 8 <= A) -> disjoint_from [(lo, SP + -2128); (p, p + 8)] A j) by (intros A j H1 H2; cbn; clear -H1 H2; lia).
    assert (FST1 : free_statics m1 T CTX).
    { eapply free_statics_transport; [exact FST| exact MU1| intros A j H; unfold A_IA, A_IA_INIT in H; apply DJ1; clear -H LOIMG PL; lia| | |]; apply DJ1; clear -CX0 CX1 T0 T1 AST ASC APT APC SPL LOIMG PL RNG KB; lia. }
    dpose FST1 as (_ & _ & _ & _ & QM1 & GF1 & FL1 & PS1).
    Ltac tr1 H MU WM DJ := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ].
    assert (HW01 : rw_cells asegs m1 (p + -16) (hdr_w0 b1 3)) by (tr1 HW0 MU1 WM1 DJ1; cbn; clear -APS SPL KB; lia).
    assert (HW11 : rw_cells asegs m1 (p + -12) (hdr_rest n ctx)) by (tr1 HW1 MU1 WM1 DJ1; cbn; clear -APS SPL KB; lia).
    assert (SH1 : rw_cells asegs m1 (0x7fff8000 + p / 8) [CB (Z.to_nat k) junk]).
    { tr1 SH MU1 WM1 DJ1; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -RNG PL PH KB LOIMG; lia. }
    (* [comment removed for export] *)
    eapply evtA_mono.
    { rewrite HK in SH1.
      eapply (put_A AL IMG ALWF CS CSOK ASB) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (lo := lo) (STK := SP + -2128) (junk := junk);
        first [exact HW01 | exact HW11 | exact SH1 | exact QM1 | exact GF1 | exact FL1 | exact PS1 | exact ST1 | exact LOIMG | exact MI1 | exact PA | exact NB | exact STAL
              | rewrite <- HK; exact PCS
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -PL; lia | rewrite <- HK; clear -PH KB; lia | clear -SPL LOIMG SPH; lia | clear -T0; lia | clear -T1; lia
              | clear -RNG HK PH KB; lia | clear -SPL; lia | clear -SPH; lia | rewrite <- HK; clear -APS SPL KB; lia ]. }
    cbv beta zeta. (intros ms2 dd_H; ddestruct dd_H as (x5 & x6 & x7 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & -> & MU2 & WM2 & MI2 & PFR2 & SHF2 & PS2 & ST2)).
    rewrite <- HK in MU2, SHF2.
    assert (SR : 0x800c3e00 <= 0x7fff8000 + p / 8 /\ 0x7fff8000 + p / 8 + k <= 0x10007fff0000).
    { pose proof (Z.div_mod p 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound p 8 ltac:(clear; lia)). pose proof aceil_bounds. clear -H H0 H1 RNG PL PH KB. lia. }
    unfold fsegP0_post. rewrite <- HK. cbv zeta.
    dexists x5, x6, x7, x15, x16, x17, x28, x29, x30, x31, m2. split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
    split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|]. split; [exact PFR2|]. split; [exact SHF2|].
    split; [eapply wr_at_transport; [exact WR1| exact WM2]|].
    split.
    { assert (DJ2 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= 0x7fff7000 \/ 0x10007fff0000 <= A) -> disjoint_from [(lo, SP + -2128); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k)] A j)
        by (intros A j H1 H2; cbn; clear -H1 H2 SR; lia).
      eapply free_statics_transport; [exact FST1| exact MU2| intros A j H; unfold A_IA, A_IA_INIT in H; cbn; clear -H LOIMG SR; lia| | |]; cbn; clear -CX0 CX1 THI T1 CTXNS SPL LOIMG KB SR; lia. }
    exact ST2.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition fsegPA_W (p lo SP T last n : Z) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "(15.(16.$4.$4.)(17.$4.$4.O5.(5.O4.-850.))(15.(16.$4.$4.)(17.$4.$4.O6.(5.O6.+8.))(15.(16.$4.$4.)(17.$4.$4.(5.+7???8000.(6.O6.+8.))(5.(5.+7???8000.(6.O6.+8.))(6.(5.O1.+7.)+8.)))(15.(16.$4.$4.)(17.$4.$4.(5.O3.+50.)(5.O3.+70.))(15.(16.$4.$4.)(17.$4.$4.O2.(5.O2.+2000.))(18.(16.$4.$4.)))))))")
(* [comment removed for export] *).

  Definition fsegPA_post (SP : Z) (gp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (p n lo T len first last bytes bsize : Z) (elems : list word) (mC : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))ZSTK,$4.(5.O15.-850.)(7.(8.$0.R12.(9.(:.(;.&40.$<.)(;.&40.(5.R1.-50.))O14.(;.&40.$=.)R11.R10.R?.(;.&40.(5.$>.+2=8.))(;.&40.(5.O8.+50.))R>.R=.R<.R;.R:.R9.R8.R7.(;.&40.O:.)(;.&40.R1.)(;.&40.(5.O8.+=0.))(;.&40.(5.O;.-10.))(;.&40.$?.)O12.O11.O10.O?.O>.R6.R5.R4.R3.)O=.(;.&40.$<.)O<.(11.(2.&40.))R2.(12.$13.)))(7.(14.(37.O;.O9.O15.O8.O5.O:.)O1.R2.)(7.(19.$13.O1.R2.)(7.(1:.$13.R2.)(7.(25.$13.R2.O9.(5.R1.-50.))(7.(1;.R2.R1.O8.R1.O13.(;.&40.(5.O15.-51.))(;.&40.R1.)(;.&40.+1.)(;.&40.$1<.)(;.&40.O;.)(;.&40.O15.)(;.&40.$1=.))(7.(23.$13.R2.O;.+8.)(7.(1>.$13.R2.(5.+7???8000.(6.O;.+8.))(15.$1?.(20.(21.(6.(5.O:.+7.)+8.))(22.(2.&8.)(;.&8.+?=.)(21.(6.(5.O:.+7.)+8.))))(18.$1?.)))(7.(1>.$13.R2.(5.O8.+50.)(38.O7.O6.O5.(5.O4.O:.)))(7.(1>.$13.R2.O5.(39.=(5.O3.O:.)(5.(3:.(3;.(2.&40.)O2.))+1.)))(7.(3<.$13.R2.(5.O5.+18.)(3=.(2.&40.)O2.(15.(2.&40.)(;.&40.(5.O;.-10.))(18.(2.&40.)))))(23.$13.R2.O5.+2000.))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "03h0@L11367354891.4  L11367568812.3  L11367586056.4  L11367586059.5  L11367587336.4  L11367587339.7  L11369327115.4  L11369327496.3  L11369458568.4  L11369484986.4  L11369566906.9  L11369622408.4  L12137473770.6  L12137652708.2  L1214218871.3   L1216166900.3   L1216330740.3   L12297272267.21 L15515971117.8  L1603916885.4   L1603950677.6   L1603950678.3   L1603952469.4   L1603952470.3   L1605899492.7   L1605981412.3   L1606020566.3   L1606118870.3   L16440599499.13 L17410157662.2  L18641020606.11 L19167748205.8  L20526482804.10 L21049500170.6  L22206244445.3  L22206275439.3  L22206324591.8  L22206408285.3  L22206637661.2  L22206638046.3  L22208339934.4  L22208566237.3  L22208566238.6  L22208566493.3  L22208566494.4  L22406284478.4  L23062806686.7  L24893985869.10 L25426245911.7  L25426245911.9  L26870639355.8  L26880640045.2  L27695573260.11 L27846297964.3  L28573891711.8  L29949905540.9  L30523802039.2  L30524034484.4  L30525977655.3  L30526141495.3  L31735977102.21 L33686401973.1  L34654488613.6  L34654717497.5  L34654767773.4  L34654767774.5  L34654768541.4  L34654768542.7  L34654798238.5  L34656516125.4  L34656516510.5  L34656811037.4  L34656909341.4  L34656928047.4  L34656977199.9  L35787266409.5  L35787266409.8  L35787266413.5  L35788968035.10 L35788968035.8  L35789379437.5  L35789449426.7  L36641975057.5  L36641975058.3  L36642203409.4  L36644134546.3  L36644218784.6  L36644267936.2  L36644298386.3  L36644364462.3  L36684221871.9  L36949723459.4  L36967530425.11 L38237949960.3  L39485528716.6  L39485528719.4  L39485529484.3  L39485529487.3  L39485625996.5  L39487565583.4  L39487729423.4  L40938924652.1  L42627424012.7  L42627473164.3  L42627504130.3  L42629649926.6  L42726802815.2  L43865612567.8  L43867762451.3  L43867820204.5  L43868104733.6  L43868104733.8  L4487909479.8   L4487991399.3   L4488030549.3   L4488128853.3   L4488423638.4   L4488423765.3   L4490121430.4   L4490157013.3   L4490157014.4   L4490157269.3   L4490157270.6   L4490172273.4   L4490402157.6   L4491675308.13  L45708238342.11 L46532565131.2  L46730492011.7  L47886762873.1  L49182591458.4  L49182591458.5  L49182591458.6  L49182591462.3  L49182591462.7  L49182736477.4  L49182820346.3  L49182837597.4  L49182837598.3  L49182837853.6  L49182837854.3  L49184716893.3  L49184716893.4  L49184717278.2  L49184817388.8  L49184848350.3  L49184866540.3  L49185012190.3  L50097029659.7  L51794544653.3  L52412055292.5  L52412068440.5  L52412068443.6  L52412069208.5  L52412069211.8  L52412234075.5  L52412346592.4  L52412346592.7  L52412346596.4  L52412346596.5  L52412346596.6  L52414218456.5  L52414314986.10 L52414316760.5  L52414364138.5  L52414447832.5  L52414447963.6  L54389223275.11 L56786826630.8  L57628699659.8  L59731263574.3  L59731376359.3  L59731395029.3  L59731425511.8  L59731493333.3  L59733506134.4  L59733668693.3  L59733668694.4  L59733668949.3  L59733668950.6  L61028792521.97 L61031298166.142L61045092046.21 L61123023741.10 L61536368211.4  L61538482263.6  L61745276307.4  L61745276311.4  L61745276311.7  L61746982045.8  L61747063965.5  L61747424147.4  L61747483692.6  L62391680077.21 L63374621462.143L63374621462.98 L63995254982.8  L64146542324.21 L64181499405.21 L65337180824.11 L66552202845.8  L66552284765.4  L66552381779.4  L66554433367.6  L66774298937.3  L67172332582.3  L67172381734.7  L67172748439.3  L67172823848.3  L67174874412.7  L67267330474.11 L6744778266.5   L67448774383.11 L6744877593.3   L6744877594.5   L6746873753.4   L6747037593.4   L68242401234.3  L68242565074.2  L68354050849.0  L7064433807.13  L8658659494.4   L8658822053.2   L8658822309.3   L8658822310.6   L8660750629.3   L8660848933.3   L902536667.4    L902536667.7    L902536671.4    L902536671.5    L902583392.6    L902763463.5    L902813792.8    L902813795.5    L902815584.6    L902815587.5    L904555616.5    L904556003.4    L904687075.5    L904713425.5    L904762577.10   L904850915.5    L9173359281.11  L9265737838.6   L9267362148.3   L9267444068.7   L9267789418.3   00000100=00>00?00@00A00B00C00D00E00F00G00X00Y00g00h00i01f02:02;02<02=02>02?02S02T02U02V02i03103I03]03o04;04<04=04>04?04E04F04G04H04I04J04K04V04j05?05R05j06:06;06O06V06m07D07O07P07Q07R07m08008?08@08A08B08C08D08E08F08G08H08I08J08K08L08M08N08O08c08d08e08k08l08m08n08o09509609709R09W09k09o0:00:10:>0:?0:@0:A0:B0:E0:F0:G0:H0:T0:U0:V0:W0:X0:Y0:n0:o0;00;10;20;30;40;50;60;70;80;90;:0;F0;b0<90<?0<F0<I0<J0<K0<L0<M0<N0<O0<P0<Q0<R0<S0<T0<U0<b0<c0<d0<e0<f0<g0=80=@0=A0=B0=C0=D0=E0=F0=G0=H0=I0=Y0=Z0=[0=\0=]0=^0=_0=`0=n0>10>H0>R0>S0>T0>U0>V0>W0>X0>Y0>Z0>[0?00?E0?`0@50@60@E0@F0@G0@H0@\0@]0@^0@_0A80AM0Ab0Ae0B;0BT0Bl0Bm0Bn0Bo0C>0C?0C@0CA0CK0CL0CM0CW0CX0D00D10D>0D?0D@0DA0DK0DL0Dl0Dm0E80E90E:0E;0E<0E=0E>0E?0EL0EM0EN0EO0EP0EQ0ER0ES0ET0EU0EV0EW0EX0Ek0FD0FE0FF0FGFS1T4last3ALTFFFFFFFFFFS3hAR1p1n1k2PH2KBFS3hAR4last3LA1FFS3hAR2SP1p1n2lo1T3CTX1k2PL3RNG2T02T13CX13APT3APC5LOIMG3SPL2KBS2SP1p1n2lo1k3APS2KBFFFFFS3hAR1p1n1k2PL2PH2KBFFFS4last5elems3LHI2ELS3len2L0S3hAR2SP1p2lo1k5LOIMG2SRS2SP1p1n2lo1k3APS2KBS3hAR1p1T1k3THI2SRS3hAR1p1k2PHFFFFS1T2T0FFFFFFS1n2NB1H2H0S2SP2lo4last3ASL3SPLS3hAR1p4last1k3LHI2SRS2SP1p2lo1A1j2H12H2S2SP1p2lo1k2SR1A1j2H12H2S3hAR1p2PL1A1j1HFS1p1n1T1k3THI3APT2KBS2SP2loS2SP1p2lo1T4last1k1y2HyS3hAR2SP2lo5LOIMG1A1j1HS5bytes3BY0FFFS3hAR1p1n1T3CTX1k2T03APC2KBS1TS3hAR2SP2lo3SPLFFFFFFFFFFFFFFFFS2SP1p1n2lo1k3APS2KBFFS1n2NBFFFFS1n2NBFFS2SP2lo1T4last1A1j2H12H22H3S1p1kS3hAR1p1k2PL2PH1H2H0S2loFFS1n5bsize3BS1FFFFS1pFFFS3hAR2SP3SPHFFFFFS3hAR1p1n1k3RNG2HK2KBFFFFFFFFFFFFS3hAR2SP3SPHS1p1n4last5elems1k2EL3ALP2KBS2SP1n2lo4last1k3ASL2KBS1p2PLS2SP2loS1TFFFFFFFFFFFFS3hAR1T2T02T1FFFFFS2SP2lo1T3AST3SPLS1n1k2KBFFFFFFFFFS2SP2lo4last3ASLFFFFFFFS1n1T1k3THI2KBS1pS2SP1p2lo1T4last1k1y2HyS3hAR1T2T1FFFFFFFFFS3hAR2SP1p1n5elems2ELS3hAR2SP1p1n5elems2ELS3hAR1p1n1T3CTX1k2T03APC2KBS3hAR1p1n1k2PH3RNG2KBFS3hAR2SP2lo3SPLFFFS2SP1p1n2lo1k3APS2KBFFFS3hAR2SP2lo3CTX3CX15LOIMGS3hAR2SP1p1n5elems2ELS3hAR2SP1p1n5elems2ELS1pS3hAR2SP2lo1T2T15LOIMGS3hAR2SP2lo3CTX3CX15LOIMGS3hAR2SP1p2lo1k2PH5LOIMGFFFS3hAR2SP2lo3SPLFFFS3hAR1T2T1FFS4last3LHIFS2SP1n2lo1T1k3THI3AST2KBFS1n5bytes3BY1FFFS5first2F0SS2SP1n2lo4last5elems1k2EL3ASL2KBFS5bsize3BS0FFFFFFFS2SP2lo1T3ASTFFFFFFFFFFFFS1p1n4last1k3ALP2KBS3hAR2SP2lo5LOIMG3SPL3SPHFFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma fsegPA : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "Pgp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pidw,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$4.Pp,$4.Pb1,$4.Pn,$4.Pctx,$4.Plo,$4.PT,$4.PCTX,$4.Plen,$4.Pfirst,$4.Plast,$4.Pbytes,$4.Pbsize,$4.Pelems,(26.(2.&40.))Pjunk,(26.(2.&8.))PF,(27.&5.(2.&40.))Pfc,(2.&20.)PmC,P,(2.&40.)(3.(2.&8.))ZSTK,$4.(5.R12.-850.)Zk,$4.(6.(5.R10.+7.)+8.)P,(28.(5.+65?000.+10.)R13.)P,(28.(5.R14.(29.+8.R2.))(2:.VhAR,))P,(8.$4.(2;.R15.+10.)=)P,(7.(28.=R14.)(28.R14.(2<.+2.+1<.)))P,(2=.(7.(28.(5.R17.+8.)+7???8000.)(28.(5.R17.(29.+8.R5.))+7???8000.))(7.(28.+10007???8008.R17.)(28.(5.R17.+8.)(2<.+2.+2?.))))P,(7.(7.(28.+1000.R13.)(2=.(28.(5.R13.+1000.)+10000.)(28.+65?000.R13.)))(2=.(28.(5.R13.+1000.)+7???7000.)(28.+10007???8000.R13.)))P,(28.+10007???8000.R10.)P,(7.(28.+1000.R15.)(2=.(28.(5.R15.+1000.)+10000.)(28.+65?000.R15.)))P,(28.(5.R16.+1000.)(2:.VhAR,))P,(28.+65?000.R16.)P,(28.(5.R17.+10000.)(2:.VhAR,))P,(1>.$13.R>.(5.R1>.-10.)(2>.R1=.+3.))P,(1>.$13.R?.(5.R1?.-<.)(2?.R1=.R1<.))P,(23.$13.R10.R20.+8.)P,(30.VCS,(5.R21.-10.)(5.+10.(29.+8.(31.R?.+1.))))P,(1>.$13.R12.(5.+7???8000.(6.R22.+8.))(15.$1?.(20.(21.R10.)R15.)(18.$1?.)))P,(1>.$13.R13.(5.R12.-30.)(15.$1?.(32.(;.&40.R12.))(15.$1?.(32.(;.&40.+1.))(15.$1?.(32.(;.&40.$1<.))(15.$1?.(32.(;.&40.R23.))(15.$1?.(32.(;.&40.R24.))(15.$1?.(32.(;.&40.$1=.))(18.$1?.))))))))P,(24.R14.R1?.R1>.)P,(30.VCS,R20.+1000.)P,(7.(28.+1.R1?.)(3>.R1?.(2<.+2.+3?.)))P,(7.(28.=R1?.)(3>.R1?.(2<.+2.+40.)))P,(28.+65?000.R1?.)P,(28.(5.R20.+2000.)(2:.VhAR,))P,(28.=R20.)P,(3>.(5.R21.R29.)(2<.+2.+3>.))P,(28.=R21.)P,(3>.(5.R22.R2;.)(2<.+2.+3?.))P,(3?.(3;.(2.&40.)R22.)#3?=.)P,(1>.$13.R1?.(5.R2:.+50.)(38.R28.R27.R26.R25.))P,(1>.$13.R20.R27.(39.=R25.(3:.(3;.(2.&40.)R24.))))P,(3<.$13.R21.(5.R28.+18.)R25.)P,(23.$13.R22.R29.+2000.)P,(30.VCS,R2:.+2000.)P,(2=.(28.(5.R2?.+1000.)R2;.)(28.(5.R2;.+2000.)R2?.))P,(2=.(28.(5.R35.(29.+8.(31.R23.+1.)))R2<.)(28.(5.R2<.+2000.)(33.R35.+10.)))P,(2=.(28.(5.R31.+1000.)(33.R36.+10.))(28.(5.R36.(29.+8.(31.R24.+1.)))R31.))P,(2=.(28.(5.R31.+10000.)(33.R37.+10.))(28.(5.R37.+8.)R31.))P,(2=.(28.R39.R32.)(28.(5.R32.+10000.)R34.))P,(2=.(28.R3:.(33.R39.+10.))(28.(5.R39.(29.+8.(31.R27.+1.)))R35.))P,(2=.(28.R3;.R35.)(28.(5.R35.+1000.)R36.))P,(2=.(28.R3<.R32.)(28.(5.R32.+2000.)R37.))P,(25.$13.R2<.R38.(5.R2;.-30.))P,(28.(2:.VhAR,)R39.)P,(28.R3:.(33.R3?.+1000.))P,(28.R40.(2<.+2.+3>.))P,(8.$4.(2;.R41.+10.)=)P,(30.VCS,R3=.(33.R42.R3=.))P,(1:.$13.R32.)(34.$13.VAL,VCS,(40.R44.R5:.R4>.R4=.R4<.R4;.R4:.R49.R35.R34.R43.R41.R3?.R3>.R3<.R3;.R3:.R39.R38.R37.R33.)(9.(:.(;.&40.$36.)(;.&40.(5.R32.-30.))R5:.(;.&40.$=.)R59.R58.R57.(;.&40.(5.R43.-10.))(;.&40.R32.)R56.R55.R54.R53.R52.R51.R50.R4?.(;.&40.$>.)(;.&40.=)(;.&40.R3>.)(;.&40.(5.R44.-51.))R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.)R35.(;.&40.$36.)R34.(11.(2.&40.))R33.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros gp t0 t1 t2 idw a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx lo T CTX len first last bytes bsize elems junk
      F fc mC STK k PL PH PA NB RNG THI LHI T0 T1 CX0 CX1 HW0 HW1 WR PCS SH QFR FST TCS L0 F0 LA0 LA1 BY0 BY1 BS0 BS1 EL QC BH BE BW BCS ALT ALP APT APC ASC
      APS AST ASL ST LOIMG SPL SPH SPA SCS MI.
    assert (HK : k = (n + 7) / 8) by reflexivity. clearbody k. subst STK.
    assert (KB : 0 <= k /\ 8 * k < n + 8 + 8) by (rewrite HK; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); clear -H H0 NB; lia).
    dpose FST as (MS8 & MF & TT & C8' & QM & GF & FL & PS).
    assert (STAL : (SP + -2128) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, SPA; reflexivity).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (qc_B AL IMG ALWF CS CSOK) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (lo := lo) (STK := SP + -2128) (m0 := mC);
        first [exact HW0 | exact HW1 | exact WR | exact QFR | exact ST | exact LOIMG | exact MI | exact T0 | apply munch_refl | apply wmono_refl
              | eapply crange_sub; [exact PCS| clear; lia| clear -KB; lia]
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -PL; lia | clear -PH KB; lia | clear -NB; lia | clear -SPL LOIMG SPH; lia | clear -T1; lia | clear -SPL; lia | clear -SPH; lia
              | clear -APS SPL KB; lia ]. }
    cbv beta. (intros ms1 dd_H; ddestruct dd_H as (y16 & y17 & m1 & -> & MU1 & WM1 & MI1 & WR1 & ST1)).
    assert (DJ1 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= p \/ p + 8 <= A) -> disjoint_from [(lo, SP + -2128); (p, p + 8)] A j) by (intros A j H1 H2; cbn; clear -H1 H2; lia).
    assert (FST1 : free_statics m1 T CTX).
    { eapply free_statics_transport; [exact FST| exact MU1| intros A j H; unfold A_IA, A_IA_INIT in H; apply DJ1; clear -H LOIMG PL; lia| | |]; apply DJ1; clear -CX0 CX1 T0 T1 AST ASC APT APC SPL LOIMG PL RNG KB; lia. }
    dpose FST1 as (_ & _ & _ & _ & QM1 & GF1 & FL1 & PS1).
    assert (HW01 : rw_cells asegs m1 (p + -16) (hdr_w0 b1 3)) by (tr1 HW0 MU1 WM1 DJ1; cbn; clear -APS SPL KB; lia).
    assert (HW11 : rw_cells asegs m1 (p + -12) (hdr_rest n ctx)) by (tr1 HW1 MU1 WM1 DJ1; cbn; clear -APS SPL KB; lia).
    assert (SH1 : rw_cells asegs m1 (0x7fff8000 + p / 8) [CB (Z.to_nat k) junk]).
    { tr1 SH MU1 WM1 DJ1; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -RNG PL PH KB LOIMG; lia. }
    (* [comment removed for export] *)
    eapply evtA_cut.
    { rewrite HK in SH1.
      eapply (put_A AL IMG ALWF CS CSOK ASB) with (p := p) (b1 := b1) (n := n) (ctx := ctx) (T := T) (lo := lo) (STK := SP + -2128) (junk := junk);
        first [exact HW01 | exact HW11 | exact SH1 | exact QM1 | exact GF1 | exact FL1 | exact PS1 | exact ST1 | exact LOIMG | exact MI1 | exact PA | exact NB | exact T0 | exact STAL
              | rewrite <- HK; exact PCS
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -PL; lia | rewrite <- HK; clear -PH KB; lia | clear -SPL LOIMG SPH; lia | clear -T1; lia
              | clear -RNG HK PH KB; lia | clear -SPL; lia | clear -SPH; lia | rewrite <- HK; clear -APS SPL KB; lia ]. }
    cbv beta zeta. (intros ms2 dd_H; ddestruct dd_H as (x5 & x6 & x7 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & -> & MU2 & WM2 & MI2 & PFR2 & SHF2 & PS2 & ST2)).
    rewrite <- HK in MU2, SHF2.
    assert (SR : 0x800c3e00 <= 0x7fff8000 + p / 8 /\ 0x7fff8000 + p / 8 + k <= 0x10007fff0000).
    { pose proof (Z.div_mod p 8 ltac:(lia)). pose proof (Z.mod_pos_bound p 8 ltac:(lia)). pose proof aceil_bounds. clear -H H0 H1 RNG PL PH KB. lia. }
    assert (DJ2 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= 0x7fff7000 \/ 0x10007fff0000 <= A) -> disjoint_from [(lo, SP + -2128); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k)] A j)
      by (intros A j H1 H2; cbn; clear -H1 H2 SR; lia).
    assert (DJ12 : forall A j, (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= p \/ p + 8 <= A) -> (A + j <= 0x7fff7000 \/ 0x10007fff0000 <= A) ->
                   disjoint_from [(lo, SP + -2128); (p, p + 8)] A j /\ disjoint_from [(lo, SP + -2128); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k)] A j).
    { intros A j H1 H2 H3. split; [apply DJ1; assumption| apply DJ2; assumption]. }
    Ltac tr12 H MU1 WM1 MU2 WM2 DJ12 tac :=
      let D := fresh "D" in
      unshelve (epose proof (DJ12 _ _ _ _ _) as D); [| | | | | destruct D as [?D1 ?D2];
        eapply rw_cells_transport; [eapply rw_cells_transport; [exact H| exact MU1| exact WM1| exact D1]| exact MU2| exact WM2| exact D2]]; tac.
    assert (QC2 : rw_cells asegs m2 (T + 80) (qc_cells len first last bytes)).
    { eapply rw_cells_transport; [eapply rw_cells_transport; [exact QC| exact MU1| exact WM1|]| exact MU2| exact WM2|];
        [apply DJ1| apply DJ2]; cbn; clear -AST APT SPL THI KB; lia. }
    assert (BH2 : rw_cells asegs m2 last (batch_hdr 0 bsize (Z.of_nat (length elems)))).
    { eapply rw_cells_transport; [eapply rw_cells_transport; [exact BH| exact MU1| exact WM1|]| exact MU2| exact WM2|];
        [apply DJ1| apply DJ2]; cbn; clear -ASL ALP SPL LHI KB; lia. }
    assert (BE2 : u64arr asegs m2 (last + 24) elems).
    { eapply u64arr_transport; [eapply u64arr_transport; [exact BE| exact MU1| exact WM1|]| exact MU2| exact WM2|];
        [apply DJ1| apply DJ2]; cbn; clear -ASL ALP SPL LHI KB EL; lia. }
    assert (BW2 : wr_at asegs m2 last 8192) by (eapply wr_at_transport; [eapply wr_at_transport; [exact BW| exact WM1]| exact WM2]).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (enq_append AL IMG ALWF CS CSOK) with (C := T + 80) (len := len) (first := first) (last := last) (bytes := bytes) (bsize := bsize) (n := n) (cb := p + -16) (lo := lo) (elems := elems) (CACHE := T + 208);
        first [exact QC2 | exact BH2 | exact BE2 | exact BW2 | exact BCS | exact EL | exact ST2 | exact LOIMG | exact MI2 | exact LA0
              | eapply crange_sub; [exact TCS| clear; lia| clear; lia]
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -L0; lia | clear -F0; lia | clear -LA1; lia | clear -BY0; lia | clear -BY0 BY1 NB; lia | clear -BS0; lia | clear -BS1; lia | clear -NB; lia
              | clear -PL PH KB; lia | clear -T1; lia | clear -T0; lia | clear -ALT; lia | clear -SPL LOIMG SPH; lia | clear -SPL; lia | clear -SPH; lia
              | clear -AST SPL; lia | clear -ASL SPL; lia | clear -T0 T1; lia ]. }
    cbv beta. (intros ms3 dd_H; ddestruct dd_H as (z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & m3 & -> & MU3 & WM3 & MI3 & QC3 & BH3 & BE3 & BW3 & ST3)).
    replace (ret_pc (Z_to_bv 64 A_QPUT_RA1)) with (Z_to_bv 64 A_QPUT_RA1) by (unfold A_QPUT_RA1; symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (DJ3 : forall A j, (A + j <= lo \/ SP + -2128 + -80 <= A) -> (A + j <= T + 80 \/ T + 112 <= A) -> (A + j <= last \/ last + 8192 <= A) ->
                  disjoint_from [(lo, SP + -2128 + -80); (T + 80, T + 80 + 32); (last, last + 8192)] A j) by (intros A j H1 H2 H3; cbn; clear -H1 H2 H3; lia).
    assert (PFR3 : put_frame m3 (SP + -2128) T (SP + -2128) s6 (Z_to_bv 64 (SP + -81)) (Z_to_bv 64 (SP + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 A_PC_FREE) (Z_to_bv 64 p) (Z_to_bv 64 SP) (Z_to_bv 64 A_FREE_RA2)).
    { unfold put_frame in *. eapply rw_cells_transport; [exact PFR2| exact MU3| exact WM3| apply DJ3; cbn; clear -AST ASL SPL; lia]. }
    (* [comment removed for export] *)
    apply evtA_done. unfold fsegPA_post, fsegPA_W. rewrite <- HK. cbv zeta.
    dexists x5, x6, x7, z10, z11, z12, z13, z14, z15, z16, z17, x28, x29, x30, x31, m3.
    split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]].
             all: unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    split; [exact PFR3|].
    split. { eapply wr_at_transport; [exact WR1| eapply wmono_trans; [exact WM2| exact WM3]]. }
    split. { eapply rw_cells_transport; [exact SHF2| exact MU3| exact WM3| apply DJ3; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -SR LOIMG THI LHI; lia]. }
    split; [exact QC3|]. split; [exact BH3|]. split; [exact BE3| exact BW3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fsegPH_W (p lo SP T last b n len : Z) : list (Z * Z) :=
    [(lo, SP + -2128); (p, p + 8); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + (n + 7) / 8);
     (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (b, b + 32); (last, last + (if len =? 0 then 0 else 8))].

  Definition fsegPH_post (SP : Z) (gp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (p n lo T len first last bytes b count max : Z) (csz : word) (cks : list word) (mC : mem) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (stj' : word),
      let STK := SP + -2128 in
      ms' = MS (mkR (Z_to_bv 64 A_QPUT_RA1) (Z_to_bv 64 (STK + -80)) gp (Z_to_bv 64 A_TP) t0 t1 t2
                   (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 (T + 80)) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 n) (Z_to_bv 64 STK) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (p + -16)) (Z_to_bv 64 kQuarantineCache)
                   s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 A_QPUT_RA1) fc None m' (seg_rom asegs)
      /\ munch (fsegPH_W p lo SP T last b n len) mC m' /\ wmono asegs mC m' /\ mem_inv asegs m' /\ stk asegs m' lo (STK + -80)
      /\ put_frame m' STK T STK s6 (Z_to_bv 64 (SP + -81)) (Z_to_bv 64 STK) (Z_to_bv 64 1) (Z_to_bv 64 A_PC_FREE) (Z_to_bv 64 p) (Z_to_bv 64 SP) (Z_to_bv 64 A_FREE_RA2)
      /\ wr_at asegs m' p 8
      /\ rw_cells asegs m' (0x7fff8000 + p / 8) [CB (Z.to_nat ((n + 7) / 8)) (repeat (Z_to_bv 8 0xfd) (Z.to_nat ((n + 7) / 8)))]
      /\ rw_cells asegs m' (T + 80) (qc_cells (len + 1) (if len =? 0 then b else first) b (bytes + (n + 8192)))
      /\ rw_cells asegs m' (T + 2128) (pc24_cells (count - 1) max csz) /\ u32arr asegs m' (T + 2144) cks
      /\ rw_cells asegs m' (T + 2784) [C8 stj']
      /\ rw_cells asegs m' b (batch_hdr 0 (n + 8192) 1) /\ u64arr asegs m' (b + 24) [Z_to_bv 64 (p + -16)] /\ wr_at asegs m' b 8192
      /\ (len <> 0 -> rw_cells asegs m' last [C8 (Z_to_bv 64 b)]).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01a0?L10121807515.5 L11210538603.11L11932576012.11L1216200700.12 L13074888347.8 L14202062195.2 L1605899492.7  L16622136815.11L17120848823.0 L18641020606.7 L19099076589.6 L20180885231.11L20526482804.5 L21154858708.6 L21652702970.2 L22406284478.4 L22706556426.11L22752009081.12L22790857345.5 L23060509866.5 L24056729556.6 L24893843434.5 L26629940037.11L26876924998.10L27695573260.11L27846297964.3 L28573891711.11L2922588682.3  L29306133812.5 L2932921898.2  L2935171342.3  L2935302285.4  L29935465330.3 L29952013369.10L30477967372.11L32481986978.11L32939732843.11L33029157746.15L33908371993.3 L34652715801.4 L34654488609.3 L34654488613.6 L34654750521.4 L34656516510.5 L34656909341.4 L36419772449.4 L36420166050.2 L36644267936.2 L36841451887.5 L36967530425.11L37561199382.11L38237949960.3 L38952874260.5 L39332637397.0 L39576446894.15L41695192000.8 L41717901008.4 L42229491618.5 L42587408084.6 L4483836497.3  L4488030549.3  L4488423638.4  L4490139249.3  L4490402157.2  L4490402157.6  L45708370748.11L46732241046.2 L47794956744.15L48321142004.5 L48543396678.1 L50097029659.5 L51485124203.11L51794544653.3 L52414186704.12L53107610470.5 L53843797014.8 L54389223275.11L55302017234.3 L55302410577.4 L55306212310.2 L56675862979.8 L56884286959.11L58931247116.11L59899730139.5 L6118669036.10 L6365922200.5  L63687859465.4 L64310949844.6 L64512570430.12L64545716713.12L64602042094.15L65602136924.1 L67109586865.15L67162524718.15L67172748439.3 L67267214480.11L67448774383.11L68354050849.0 L8806423876.11 L9173231499.11 L9265479538.3  L9265737838.6  L9267314774.3  L9267708373.4  L9271509842.3  L9479837216.4  L9479837216.7  L9479837220.4  L9479837220.5  L9480100156.5  L9481955227.5  L9482085912.5  L9494668572.5  00000A00O00c01001C01I01]02502602N02d03<03J03`03k04604V04e05205E05[05k06;06J06^06e07E07F07T07_07`07a07i08>08R08X08f09:09D09E09P09_09`09a09b09c09k0:10:>0:R0:f0:j0;90;:0;K0;U0;f0<70<M0<N0<O0<P0<Q0<Y0<e0=;0=B0=W0=e0=k0><0>J0>R0>e0?:0?F0?T0?U0?V0?a0@:0@R0@f0A70AF0AS0A`0B60BC0BR0Bc0Bi0C:0CK0CU0C^0D60D70DW0Di0Dj0EC0ED0EE0EF0EG0EH0EI0EV0EW0EX0EY0EZS2SP2lo1T3AST3SPLS1n1T1k3THI2KBS1p1n1T1k3THI3APT2KBS3hAR4last2D4S3hAR2SP1p2lo5LOIMGS1A2H1S3hAR1p1n1k2PL2PH2KBS2SP1n2lo1T1k3THI3AST2KBSS3hAR2SP1p2lo1k5LOIMG2SRS3hAR2SP2lo1b2B15LOIMGS2SP1n2lo1T1k3THI3AST2KBS1p1T1k3THI2SRS3hAR2SP2lo1T2T15LOIMGS5count3CNTS1n2NB1H2H0S2SP1p2lo1T3len4last1k1b2lw1y2HyS3hAR1T4last2D5S1p1k1b2B02SRS2SP2lo4last3SPL2D8S3hAR2SP2lo1T2T15LOIMGS1p4last1k2SR2D3S1p1n1k1b3ABP2KBS1p1k2SR1A1j2H3S1p1n1T1k3THI3APT2KBS2SP2loS2SP1p2lo1T3len4last1k1b2lw1y2HyFS1p1T1k3THI2SRS5count3CNTFFS1p1k2SRS2SP1p2lo1k2SR1A1j2H2S1p1n1T1k3THI3APT2KBS1b2B0S1n1T1k3THI2KBS3len4last2lw1A1j2H6S3hAR1b2B1FS2SP2lo3SPLS3hAR2SP2lo3SPLFFFFS3len2L0S1n2NBS2SP2lo1A1j1HS3hAR1p1k2PL2PH1H2H0S2SP1n2lo1k1b3ABS2KBS2loS2SP2lo4last2D8SS1T3len2lw1A1j2H2S3hAR1p2PLS3hAR2SP2lo5LOIMGS2SP2lo1b3ABS3SPLS3hAR2SP2lo1T2T15LOIMGFFFFS2SP3SPHS3hAR2SP3SPHS2SP1n2lo4last1k2KB2C8S2SP2loS2SP2lo3len2lw1A1j2H1S1p1T1k3THI2SRS4lastS2SP2lo1T3AST3SPLS1n1T1k3THI2KBS1n1k2KBS3hAR2SP2lo4last2D8S3hAR2SP2lo5LOIMG3SPLS3hAR1p1k2SRS1n1T1k3THI2KBFFS4last4LA64S3hAR2SP2lo4last2C32C42C8S2SP1n2lo1T1k3THI3AST2KBS1p1n1T1k3THI3APT2KBS2SP2lo1T3AST3SPLS1p1k2SR1A1j2H1S2SP2lo1b3ABSS4last1A1j2H2S3hAR2SP2lo1T2T15LOIMGS3hAR4last2D3S3hAR4last1b2D6S1T3len2lw1A1j2H3S4lastS3len1b2lw1A1j2H5S1T3len2lw1A1j2H4S3hAR1T2T1S4last2C3S2SP1n2lo1T1k3THI3AST2KBSS2SP1p2lo1T3len4last1k1b2lw1y2HyS1p1n4last1k2KB2C7FS3hAR2SP2lo5LOIMG3SPL3SPHFFFFFFS2SP2lo1T3ASTFFFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma fsegPH : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "Pgp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pidw,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pstj,(2.&40.)Pcsz,(2.&40.)Plnext,(2.&40.)Plsize,(2.&40.)Pj0,(2.&40.)Pj1,(2.&40.)Pj2,(2.&40.)Pj3,(2.&40.)PSP,$4.Pp,$4.Pb1,$4.Pn,$4.Pctx,$4.Plo,$4.PT,$4.PCTX,$4.PSB,$4.Plen,$4.Pfirst,$4.Plast,$4.Pbytes,$4.Plcount,$4.Pcount,$4.Pmax,$4.Pck,$4.Pcks,(26.(2.&40.))Pjunk,(26.(2.&8.))PF,(27.&5.(2.&40.))Pfc,(2.&20.)PmC,P,(2.&40.)(3.(2.&8.))ZSTK,$4.(5.R16.-850.)Zk,$4.(6.(5.R14.+7.)+8.)Zb,$4.(5.(5.R10.+1800000000.)(29.+10.R8.))P,(28.(5.+65?000.+10.)R18.)P,(28.(5.R19.(29.+8.R3.))(2:.VhAR,))P,(8.$4.(2;.R1:.+10.)=)P,(7.(28.=R19.)(28.R19.(2<.+2.+1<.)))P,(2=.(7.(28.(5.R1<.+8.)+7???8000.)(28.(5.R1<.(29.+8.R6.))+7???8000.))(7.(28.+10007???8008.R1<.)(28.(5.R1<.+8.)(2<.+2.+2?.))))P,(7.(7.(28.+1000.R18.)(2=.(28.(5.R18.+1000.)+10000.)(28.+65?000.R18.)))(2=.(28.(5.R18.+1000.)+7???7000.)(28.+10007???8000.R18.)))P,(7.(28.+1000.R19.)(2=.(28.(5.R19.+1000.)+10000.)(28.+65?000.R19.)))P,(28.(5.R1:.+1000.)(2:.VhAR,))P,(8.$4.(2;.R1;.+1000.)=)P,(28.+65?000.R1;.)P,(28.(5.R1<.+10000.)(2:.VhAR,))P,(1>.$13.R?.(5.R23.-10.)(2>.R22.+3.))P,(1>.$13.R10.(5.R24.-<.)(2?.R22.R21.))P,(23.$13.R11.R25.+8.)P,(30.VCS,(5.R26.-10.)(5.+10.(29.+8.(31.R10.+1.))))P,(1>.$13.R13.(5.+7???8000.(6.R27.+8.))(15.$1?.(20.(21.R11.)R16.)(18.$1?.)))P,(1>.$13.R14.(5.R13.-30.)(15.$1?.(32.(;.&40.R13.))(15.$1?.(32.(;.&40.+1.))(15.$1?.(32.(;.&40.$1<.))(15.$1?.(32.(;.&40.R28.))(15.$1?.(32.(;.&40.R29.))(15.$1?.(32.(;.&40.$1=.))(18.$1?.))))))))P,(24.R15.R24.R23.)P,(30.VCS,R25.+1000.)P,(2=.(28.(5.R26.+1000.)(33.R2;.+10.))(28.(5.R2;.(29.+8.(31.R15.+1.)))R26.))P,(2=.(28.(5.R26.+10000.)(33.R2<.+10.))(28.(5.R2<.+8.)R26.))P,(2=.(28.R2>.R27.)(28.(5.R27.+10000.)R29.))P,(2=.(28.(5.R28.+10000.)+7???8000.)(28.+10007???8000.R28.))P,(2=.(28.R30.(33.R2?.+10.))(28.(5.R2?.(29.+8.(31.R19.+1.)))R2;.))P,(2=.(28.R31.R2;.)(28.(5.R2;.+1000.)R2<.))P,(7.(28.=R29.)(3>.R29.(2<.+2.+3>.)))P,(7.(28.=R29.)(3>.R29.(2<.+2.+40.)))P,(7.(28.=R29.)(3>.R29.(2<.+2.+40.)))P,P,(8.$4.R2<.=)(8.$4.R2;.=)P,(28.=R2:.)P,(3>.(5.(5.R2;.R34.)+2000.)(2<.+2.+3?.))P,(2=.(8.$4.R2?.=)(8.$4.R2;.+3?=.))P,(1>.$13.R24.(5.R33.+50.)(38.R30.R2?.R2>.R2=.))P,P,(41.(8.$4.R31.=))(7.(1>.$13.R26.R30.(15.$1?.(32.R41.)(15.$1?.(32.R40.)(15.$1?.(32.(;.&40.R2>.))(18.$1?.)))))(7.(30.VCS,R30.+18.)(7.(28.+10007???8000.R30.)(7.(28.(5.R30.+2000.)(2:.VhAR,))(7.(2=.(28.(5.R35.+1000.)R30.)(28.(5.R30.+2000.)R35.))(7.(2=.(28.(5.R23.+2000.)R30.)(28.(5.R30.+2000.)R23.))(7.(2=.(28.(5.R3:.(29.+8.(31.R24.+1.)))R30.)(28.(5.R30.+2000.)(33.R3:.+10.)))(2=.(28.R3;.R30.)(28.(5.R30.+2000.)R36.)))))))))P,(7.(28.+1.R2=.)(28.R2=.+10.))P,(7.(28.=R2=.)(3>.R2=.(2<.+2.+20.)))P,(8.$42.(3;.(2.&40.)R2<.)#10.)P,(8.(3.(2.&40.))(43.(2.&40.)R2=.(21.(33.R30.+1.)))(44.(2.&40.)(;.&40.R2>.)))P,(7.(28.=R2?.)(3>.R2?.(2<.+2.+20.)))P,(1>.$13.R2;.(5.R3:.+850.)(45.R32.R31.R47.))P,(46.$13.R2<.(5.R3;.+860.)R30.)P,(1>.$13.R2=.(5.R3<.+:>0.)(15.$1?.(32.R4:.)(18.$1?.)))P,(47.$13.R2>.$48.(15.$1?.(32.(;.&40.R3;.))(18.$1?.)))P,(3>.=R3<.)P,(28.+10007???8000.R2=.)P,(28.(5.R2>.+2000.)(2:.VhAR,))P,(1>.$13.R32.R2?.(15.$1?.(32.R4;.)(15.$1?.(32.R4:.)(15.$1?.(32.R49.)(15.$1?.(32.R48.)(18.$1?.))))))P,(23.$13.R33.R30.+2000.)P,(30.VCS,R31.+2000.)P,(2=.(28.(5.R44.+1000.)R32.)(28.(5.R32.+2000.)R44.))P,(2=.(28.(5.R4:.(29.+8.(31.R34.+1.)))R33.)(28.(5.R33.+2000.)(33.R4:.+10.)))P,(2=.(28.R4<.R34.)(28.(5.R34.+2000.)R47.))P,(25.$13.R38.R48.(5.R37.-30.))P,(28.(2:.VhAR,)R49.)P,(28.R4:.(33.R4?.+1000.))P,(28.R50.(2<.+2.+3>.))P,(8.$4.(2;.R51.+10.)=)P,(30.VCS,R4=.(33.R52.R4=.))P,(1:.$13.R3>.)(34.$13.VAL,VCS,(49.R54.R72.R66.R65.R64.R63.R62.R61.R41.R40.R53.R51.R4?.R4>.R4;.R4:.R49.R48.R3<.R46.R45.R5;.R43.R3?.)(9.(:.(;.&40.$36.)(;.&40.(5.R3>.-30.))R72.(;.&40.$=.)R71.R70.R6?.(;.&40.(5.R53.-10.))(;.&40.R3>.)R6>.R6=.R6<.R6;.R6:.R69.R68.R67.(;.&40.$>.)(;.&40.=)(;.&40.R4>.)(;.&40.(5.R54.-51.))R66.R65.R64.R63.R62.R61.R60.R5?.R5>.R5=.)R41.(;.&40.$36.)R40.(11.(2.&40.))R3?.(12.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros gp t0 t1 t2 idw a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 stj csz lnext lsize j0 j1 j2 j3
      SP p b1 n ctx lo T CTX SB len first last bytes lcount count max ck cks junk F fc mC STK k b
      PL PH PA NB RNG THI T0 T1 TAL CX0 CX1 HW0 HW1 WR PCS SH QFR FST TCS APT APC ASC CTXNS APS AST
      L0 F0 LA64 LZ BY0 BY1 NEW QC LST CNT MX LCK NTH CKB PC24 CKS STJ SBC SB0 B0 B1 BJ BW BCS ABT ABP ABS
      ST LOIMG SPL SPH SPA SCS MI.
    assert (HK : k = (n + 7) / 8) by reflexivity. clearbody k.
    assert (HB : b = SB + 103079215104 + 16 * ck) by reflexivity. clearbody b. subst STK.
    assert (KB : 0 <= k /\ 8 * k < n + 8 + 8) by (rewrite HK; pose proof (Z.div_mod (n + 7) 8 ltac:(clear; lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(clear; lia)); clear -H H0 NB; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { rewrite HK in PH, PCS, SH, APT, APS, RNG.
      eapply (fsegP0 gp t0 t1 t2 idw a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP p b1 n ctx lo T CTX junk F fc mC);
        first [sassumption | cassumption | exact PL | exact PH | exact PA | exact NB | exact RNG | exact THI | exact T0 | exact T1 | exact CX0 | exact CX1 | exact HW0 | exact HW1 | exact WR | exact PCS | exact SH
              | exact QFR | exact FST | exact TCS | exact APT | exact APC | exact ASC | exact CTXNS | exact APS | exact AST | exact ST | exact LOIMG | exact SPL | exact SPH | exact SPA | exact SCS | exact MI]. }
    cbv beta zeta. (intros ms1 dd_H; ddestruct dd_H as (x5 & x6 & x7 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MU1 & WM1 & MI1 & PFR1 & SHF1 & WR1 & FST1 & ST1)).
    rewrite <- HK in MU1, SHF1.
    assert (SR : 0x800c3e00 <= 0x7fff8000 + p / 8 /\ 0x7fff8000 + p / 8 + k <= 0x10007fff0000).
    { pose proof (Z.div_mod p 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound p 8 ltac:(clear; lia)). pose proof aceil_bounds. clear -H H0 H1 RNG PL PH KB. lia. }
    (* [comment removed for export] *)
    assert (DJ1 : forall A j, (A + j <= 0x7fff7000 \/ 0x10007fff0000 <= A) -> (A + j <= lo \/ SP + -2128 <= A) -> (A + j <= p \/ p + 8 <= A) ->
                  disjoint_from [(lo, SP + -2128); (p, p + 8); (0x7fff8000 + p / 8, 0x7fff8000 + p / 8 + k)] A j).
    { intros A j H1 H2 H3. cbn. clear -H1 H2 H3 SR. repeat split; lia. }
    assert (QC1 : rw_cells asegs m1 (T + 80) (qc_cells len first last bytes)) by (eapply rw_cells_transport; [exact QC| exact MU1| exact WM1| apply DJ1; cbn; clear -THI AST APT KB SPL; lia]).
    assert (PC1 : rw_cells asegs m1 (T + 2128) (pc24_cells count max csz)) by (eapply rw_cells_transport; [exact PC24| exact MU1| exact WM1| apply DJ1; cbn; clear -THI AST APT KB SPL; lia]).
    assert (CKS1 : u32arr asegs m1 (T + 2144) cks) by (eapply u32arr_transport; [exact CKS| exact MU1| exact WM1| rewrite LCK; apply DJ1; cbn; clear -THI AST APT KB SPL; lia]).
    assert (STJ1 : rw_cells asegs m1 (T + 2784) [C8 stj]) by (eapply rw_cells_transport; [exact STJ| exact MU1| exact WM1| apply DJ1; cbn; clear -THI AST APT KB SPL; lia]).
    assert (SBC1 : ro_cells asegs m1 A_SPACEBEG_CELL [C8 (Z_to_bv 64 SB)]).
    { eapply ro_cells_transport; [exact SBC| exact MU1|]. unfold A_SPACEBEG_CELL, A_INSTANCE. cbn. clear -LOIMG PL SR. repeat split; lia. }
    assert (BJ1 : rw_cells asegs m1 b [C8 j0; C8 j1; C8 j2; C8 j3]) by (eapply rw_cells_transport; [exact BJ| exact MU1| exact WM1| apply DJ1; cbn; clear -B0 ABS ABP KB SPL; lia]).
    assert (BW1 : wr_at asegs m1 b 8192) by (eapply wr_at_transport; [exact BW| exact WM1]).
    assert (LST1 : len <> 0 -> rw_cells asegs m1 last [C8 lnext; C8 lsize; C8 (Z_to_bv 64 lcount)] /\ crange CS last 24 /\ 0x65f000 <= last /\ last + 24 <= 2^47 /\ (SP + -2128 + -80 <= last \/ last + 24 <= lo)).
    { intros NE. ddestruct (LST NE) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). split; [| split; [exact C2| clear -C3 C4 C8 SPL; lia]].
      eapply rw_cells_transport; [exact C1| exact MU1| exact WM1| apply DJ1; cbn; clear -C3 C7 C8 KB SPL; lia]. }
    clear QC PC24 CKS STJ SBC BJ BW HW0 HW1 WR SH QFR ST MI.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (enq_new AL IMG ALWF CS CSOK) with (T := T) (STK := SP + -2128) (len := len) (first := first) (last := last) (bytes := bytes) (count := count) (max := max) (lcount := lcount) (lo := lo);
        first [exact QC1 | exact PC1 | exact TCS | exact LST1 | exact ST1 | exact LOIMG | exact MI1 | exact NEW | exact T0
              | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia]
              | clear -T1; lia | clear -L0; lia | clear -LA64; lia | clear -CNT; lia | clear -SPL LOIMG SPH; lia | clear -SPL; lia | clear -SPH; lia | clear -AST SPL; lia ]. }
    cbv beta. (intros ms2 dd_H; ddestruct dd_H as (m2 & fr & (xa2 & xa6 & xa7 & ->) & MU2 & WM2 & MI2 & EFR2 & ST2)).
    assert (DJ2 : forall A j, (A + j <= lo \/ SP + -2128 + -80 <= A) -> disjoint_from [(lo, SP + -2128 + -80)] A j) by (intros A j H; cbn; clear -H; lia).
    Ltac tr2 H := eapply rw_cells_transport; [exact H| eassumption| eassumption| ].
    assert (QC2 : rw_cells asegs m2 (T + 80) (qc_cells len first last bytes)) by (eapply rw_cells_transport; [exact QC1| exact MU2| exact WM2| apply DJ2; cbn; clear -T1 LOIMG; lia]).
    assert (PC2 : rw_cells asegs m2 (T + 2128) (pc24_cells count max csz)) by (eapply rw_cells_transport; [exact PC1| exact MU2| exact WM2| apply DJ2; cbn; clear -T1 LOIMG; lia]).
    assert (CKS2 : u32arr asegs m2 (T + 2144) cks) by (eapply u32arr_transport; [exact CKS1| exact MU2| exact WM2| rewrite LCK; apply DJ2; cbn; clear -T1 LOIMG; lia]).
    assert (STJ2 : rw_cells asegs m2 (T + 2784) [C8 stj]) by (eapply rw_cells_transport; [exact STJ1| exact MU2| exact WM2| apply DJ2; cbn; clear -T1 LOIMG; lia]).
    assert (SBC2 : ro_cells asegs m2 A_SPACEBEG_CELL [C8 (Z_to_bv 64 SB)]) by (eapply ro_cells_transport; [exact SBC1| exact MU2| apply DJ2; unfold A_SPACEBEG_CELL, A_INSTANCE; cbn; clear -LOIMG; lia]).
    assert (BJ2 : rw_cells asegs m2 b [C8 j0; C8 j1; C8 j2; C8 j3]) by (eapply rw_cells_transport; [exact BJ1| exact MU2| exact WM2| apply DJ2; cbn; clear -B1 LOIMG; lia]).
    assert (BW2 : wr_at asegs m2 b 8192) by (eapply wr_at_transport; [exact BW1| exact WM2]).
    assert (PFR2 : put_frame m2 (SP + -2128) T (SP + -2128) s6 (Z_to_bv 64 (SP + -81)) (Z_to_bv 64 (SP + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 A_PC_FREE) (Z_to_bv 64 p) (Z_to_bv 64 SP) (Z_to_bv 64 A_FREE_RA2)).
    { unfold put_frame in *. eapply rw_cells_transport; [exact PFR1| exact MU2| exact WM2| apply DJ2; cbn; clear; lia]. }
    (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (enq_pop AL IMG ALWF CS CSOK) with (T := T) (SB := SB) (len := len) (first := first) (last := last) (bytes := bytes) (n := n) (cb := p + -16) (b := b) (ck := ck)
                                              (count := count) (max := max) (lo := lo) (lw := if len =? 0 then 0 else 8) (cks := cks) (m0 := m2);
        [ reflexivity | exact T0 | clear -T1; lia | exact TAL | exact L0 | exact F0 | exact LA64 | exact BY0 | exact BY1 | clear -NB; lia | clear -PL PH KB; lia
        | clear -CNT; lia | exact MX | exact LCK | clear -CNT; lia | exact NTH | exact CKB | exact SB0 | exact HB | clear -B1; lia
        | exact QC2 | exact PC2 | exact CKS2 | exact STJ2 | exact TCS | exact SBC2 | exact BJ2 | exact BW2 | exact BCS
        | intros NE; ddestruct (LST NE) as (_ & _ & D3 & D4 & D5 & D6 & D7 & D8); clear -D3 D4 D5 D6 D8 SPL; repeat split; lia
        | intros NE; destruct (LST1 NE) as (C1 & _); pose proof (proj1 (rw_cells_app asegs m1 last [C8 lnext] [C8 lsize; C8 (Z_to_bv 64 lcount)]) C1) as [X _];
          eapply rw_cells_transport; [exact X| exact MU2| exact WM2| apply DJ2; cbn; ddestruct (LST NE) as (_ & _ & _ & _ & _ & _ & _ & D8); clear -D8 SPL; lia]
        | intros NE; ddestruct (LST1 NE) as (_ & C2 & _); eapply (crange_sub CS last 24); [exact C2| clear; lia| clear; lia]
        | exact ABT | exact EFR2 | exact ST2 | exact LOIMG | clear -SPL; lia | clear -SPH; lia | clear -AST SPL; lia | clear -ABS SPL; lia
        | apply munch_refl | apply wmono_refl | exact MI2
        | eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear -SPL; lia| clear -SPL; lia] ]. }
    cbv beta. (intros ms3 dd_H; ddestruct dd_H as (z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & m3 & stj' & -> & MU3 & WM3 & MI3 & QC3 & PC3 & CKS3 & STJ3 & BH3 & BE3 & BW3 & LST3 & ST3)).
    replace (ret_pc (Z_to_bv 64 A_QPUT_RA1)) with (Z_to_bv 64 A_QPUT_RA1) by (unfold A_QPUT_RA1; symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    set (lw := if len =? 0 then 0 else 8) in *.
    assert (LW : (len = 0 -> lw = 0) /\ (len <> 0 -> lw = 8)) by (subst lw; split; intros E; [rewrite (proj2 (Z.eqb_eq len 0) E)| rewrite (proj2 (Z.eqb_neq len 0) E)]; reflexivity).
    unfold fsegPH_post, fsegPH_W. rewrite <- HK. cbv zeta. fold lw.
    dexists x5, x6, x7, z10, z11, z12, z13, z14, z15, z16, z17, x28, x29, x30, x31, m3, stj'.
    split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|]. 2: eapply munch_trans; [eapply munch_weaken; [| exact MU2]| eapply munch_weaken; [| exact MU3]].
             all: unfold sub_fp; cbn [outside]; clear; intros y Hy; lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|]. split; [exact ST3|].
    assert (DJ3 : forall A j, (A + j <= lo \/ SP + -2128 + -80 <= A) -> (A + j <= T + 80 \/ T + 112 <= A) -> (A + j <= T + 2128 \/ T + 2132 <= A) -> (A + j <= T + 2784 \/ T + 2792 <= A) ->
                  (A + j <= b \/ b + 32 <= A) -> (A + j <= last \/ last + lw <= A) ->
                  disjoint_from [(lo, SP + -2128 + -80); (T + 80, T + 112); (T + 2128, T + 2132); (T + 2784, T + 2792); (b, b + 32); (last, last + lw)] A j)
      by (intros A j H1 H2 H3 H4 H5 H6; cbn; clear -H1 H2 H3 H4 H5 H6; repeat split; lia).
    assert (LR : forall A j, 8 <= A -> (len <> 0 -> A + j <= last \/ last + 8192 <= A) -> A + j <= last \/ last + lw <= A).
    { intros A j H1 H2. destruct LW as [LW0 LW8]. destruct (Z.eq_dec len 0) as [E|NE]; [rewrite (LZ E), (LW0 E); right; clear -H1; lia|]. specialize (H2 NE). rewrite (LW8 NE). clear -H2. lia. }
    split. { unfold put_frame in *. eapply rw_cells_transport; [exact PFR2| exact MU3| exact WM3| apply DJ3; cbn].
             - clear; lia. - clear -AST SPL; lia. - clear -AST SPL; lia. - clear -AST SPL; lia. - clear -ABS SPL; lia.
             - apply LR; [clear -LOIMG SPL; lia|]. intros NE. ddestruct (LST NE) as (_ & _ & _ & _ & _ & _ & _ & D8). clear -D8 SPL. lia. }
    split. { eapply wr_at_transport; [exact WR1| eapply wmono_trans; [exact WM2| exact WM3]]. }
    split. { eapply rw_cells_transport; [| exact MU3| exact WM3| apply DJ3; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia)].
             - eapply rw_cells_transport; [exact SHF1| exact MU2| exact WM2| apply DJ2; cbn; rewrite ?Nat.add_0_r; rewrite Z2Nat.id by (clear -KB; lia); clear -SR LOIMG; lia].
             - clear -SR LOIMG; lia. - clear -SR THI; lia. - clear -SR THI; lia. - clear -SR THI; lia. - clear -SR B0; lia.
             - apply LR; [clear -SR; lia|]. intros NE. ddestruct (LST NE) as (_ & _ & D3 & _). clear -D3 SR. lia. }
    split; [exact QC3|]. split; [exact PC3|]. split; [exact CKS3|]. split; [exact STJ3|]. split; [exact BH3|]. split; [exact BE3|]. split; [exact BW3| exact LST3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  Definition fsegB_post (SP : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeSegs ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(7.(8.$0.R11.(9.(:.O13.(;.&40.O14.)O12.(;.&40.$=.)R10.R?.R>.O11.O10.R=.R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(4:.O13.)O4.(11.(2.&40.))R1.(12.$13.)))(7.(14.(15.(16.$4.$4.)(17.$4.$4.O3.O14.)O2.)O1.R1.)(7.(19.$13.O1.R1.)(7.(1:.$13.R1.)(25.$13.R1.O3.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  
  (* [comment removed for export] *)
  
End FreeSegs.

End ARUN_1.
