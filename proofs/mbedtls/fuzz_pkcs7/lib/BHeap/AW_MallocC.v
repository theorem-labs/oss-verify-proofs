(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_AllocA AW_DepotA AW_Poison AW_AllocB AW_MallocB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_MallocC () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_ASAN_INITED"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MCS_CELL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_CF_FASTUNW"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_INITED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_PTR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_ARR"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.msegA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_PC_MALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.A_ALLOCATE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.max"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MallocC.segA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "ARUN_1.MallocC.SegB.segB_post"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.lor"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "Stdlib.ZArith.BinInt.Z.shiftr"; "ARUN_1.MallocC.SegB.segC1_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "ARUN_1.MallocC.SegB.segC2_post"].

Section ARUN_1. Context {hAR : arun}.
Definition msegA_statics (m : mem) (T CTX : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "(0.(1.$2.O3.$3.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O3.$9.(4.$5.(:.(7.&40.+1>.))(8.$5.)))(0.(1.$2.O3.$;.(4.$5.(<.(7.&40.$=.))(8.$5.)))(0.(1.$2.O3.$>.(4.$5.(6.(7.&8.+1.))(8.$5.)))(0.(1.$2.O3.$?.(4.$5.(<.(7.&40.$10.))(8.$5.)))(0.(1.$2.O3.$10.(4.$5.(<.(7.&40.+1000.))(8.$5.)))(0.(1.$2.O3.$11.(4.$5.(6.(7.&8.+1.))(4.$5.(12.#3.(4.(13.&8.)(7.&8.=)(4.(13.&8.)(7.&8.=)(4.(13.&8.)(7.&8.=)(8.(13.&8.))))))(4.$5.(:.(7.&40.=))(8.$5.)))))(0.(1.$2.O3.$14.(4.$5.(<.(7.&40.$15.))(8.$5.)))(0.(1.$2.O3.$15.(4.$5.(<.(7.&40.O1.))(8.$5.)))(1.$2.O3.(16.O1.+98.)(4.$5.(<.(7.&40.O2.))(8.$5.))))))))))))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L10579485709.20L11718987021.20L11773433101.20L2512747789.20 L48917807245.20L54335213261.20L6057446157.20 L65987149837.20000001002003004005006007008SSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma msegA_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "PW,(17.$18.)Pm,P,(13.&40.)(19.(13.&8.))Pm',P,(13.&40.)(19.(13.&8.))PT,$1:.PCTX,$1:.P,(1;.R4.R2.R1.)P,(1<.R6.R5.R4.)P,PA,$1:.Pn,$1:.P,(0.(1=.+10000.R2.)(1=.(16.R2.R1.)+65?000.))(1>.R:.R3.R2.)P,(1>.R8.(16.R4.+98.)+8.)(1;.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' T CTX S MU DJ DJC. unfold msegA_statics in *.
  unfold A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW, A_GOT_PAGESZ, A_PAGESZ_CELL, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| first [exact DJC| apply DJ; cbn; lia]]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L10581581829.22L11775529221.22L2891830110.22 L29738675806.22L30591810590.22L30787687534.22L4300841669.22 L60137559518.22L6059544325.22 L63754764293.22L65985053701.2200000100200300400500600700800900:00;SSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma allocA_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "PW,(17.$18.)Pm,P,(13.&40.)(19.(13.&8.))Pm',P,(13.&40.)(19.(13.&8.))PT,$1:.PCTX,$1:.P,(1?.R4.R2.R1.)P,(1<.R6.R5.R4.)P,PA,$1:.Pn,$1:.P,(0.(1=.+10000.R2.)(1=.(16.R2.R1.)+65?000.))(1>.R:.R3.R2.)P,(1>.R8.(16.R4.+98.)+8.)(1?.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' T CTX S MU DJ DJC. unfold allocA_statics in *.
  unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| first [exact DJC| apply DJ; cbn; lia]]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L10579486094.16L16277510926.16L40211055758.16L45409267086.16L50493836942.16L51457186446.16L62473061518.16L63253116686.16L66318283150.16000001002003004005006007008009SSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma fin_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "PW,(17.$18.)Pm,P,(13.&40.)(19.(13.&8.))Pm',P,(13.&40.)(19.(13.&8.))P,(20.R2.)P,(1<.R4.R3.R2.)P,PA,$1:.Pn,$1:.P,(0.(1=.+10000.R2.)(1=.(16.R2.R1.)+65?000.))(1>.R8.R3.R2.)(20.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' S MU DJ. unfold fin_statics in *.
  unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET, A_MUSL_MEMSET, kAllocBegMagic in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section MallocC.
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
  Definition segA_post (SP : Z) (gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 : word) (F : bvmap 5 word) (fc : bv 32)
      (n lo T TOP d : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Lms',$21.(22.(13.&40.)Lt0,(13.&40.)(22.(13.&40.)Lt1,(13.&40.)(22.(13.&40.)Lt2,(13.&40.)(22.(13.&40.)La6,(13.&40.)(22.(13.&40.)La7,(13.&40.)(22.(13.&40.)Lt3,(13.&40.)(22.(13.&40.)Lt4,(13.&40.)(22.(13.&40.)Lt5,(13.&40.)(22.(13.&40.)Lt6,(13.&40.)(22.P,(13.&40.)(19.(13.&8.))Lm',P,(13.&40.)(19.(13.&8.))(22.(17.(13.&40.))Lws,(17.(13.&40.))(22.$1:.Lsize,$1:.(22.(17.(13.&8.))Lfr1,(17.(13.&8.))(22.(17.(13.&8.))Lfr2,(17.(13.&8.))ZSTK,$1:.(16.O17.-850.)(0.(23.$21.R10.(24.(25.(7.&40.+47:64.)(7.&40.(16.R1.-10.))O16.(7.&40.$26.)R?.R>.R=.(7.&40.O17.)(7.&40.O6.)(7.&40.$27.)(7.&40.O6.)(7.&40.+8.)(7.&40.R1.)(7.&40.+1.)(7.&40.+1.)R<.R;.(7.&40.$28.)(7.&40.+1.)(7.&40.R1.)(7.&40.(16.O17.-51.))O11.O10.O?.O>.O=.O<.R:.R9.R8.R7.)O8.(7.&40.$29.)O7.(2:.(13.&40.))R6.(2;.$2.)))(0.(1<.(4.(2<.$1:.$1:.)(2=.$1:.$1:.O5.O17.)(4.(2<.$1:.$1:.)(2=.$1:.$1:.(16.O4.+<60.)(16.O4.+<61.))(8.(2<.$1:.$1:.))))O1.R6.)(0.(2>.$2.O1.R6.)(0.(2?.$2.R6.)(0.(30.$2.R6.(16.O17.-38.)(4.$5.(<.O12.)(4.$5.(<.O13.)(4.$5.(<.O14.)(4.$5.(<.O15.)(4.$5.(<.O9.)(4.$5.(<.O:.)(4.$5.(<.O;.)(8.$5.)))))))))(0.(30.$2.R6.R1.(4.$5.(<.(7.&40.(16.R1.+10.)))(4.$5.(<.(7.&40.R4.))(8.$5.))))(0.(31.$2.R6.(16.R1.+10.)R5.)(0.(23.$32.(33.(13.&40.)R5.)#1>.)(0.(0.(1=.+1.R4.)(1=.R4.+1>.))(0.(1=.R4.(16.O2.+2.))(0.(30.$2.R6.(16.R1.+100.)(4.$5.(12.#708.R3.)(8.$5.)))(0.(30.$2.R6.(16.R1.+808.)(4.$5.(<.(7.&40.O17.))(8.$5.)))(0.(30.$2.R6.(16.R1.+810.)(4.$5.(12.#8.R2.)(8.$5.)))(0.(30.$2.R6.(16.R1.-10.)(4.$5.(<.(7.&40.O17.))(4.$5.(<.(7.&40.+6978<.))(8.$5.))))(0.(30.$2.R6.(16.O4.+<60.)(4.$5.(6.(7.&8.=))(8.$5.)))(0.(34.$2.R6.O5.(16.R1.-10.))(34.$2.R6.(16.O17.-10.)(35.O3.O17.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "01J0@L10060240917.107L10060240917.108L10268361782.5  L11252131807.3  L13266555807.5  L13711453752.2  L13714063045.7  L14602434450.3  L16412746017.7  L16555544494.3  L16611567972.6  L19295369323.5  L20565690987.5  L21989683525.108L22704456280.5  L22706556809.6  L23411935237.8  L23749077557.7  L23761187578.5  L24564880824.2  L24870082995.7  L24892837319.2  L24897143244.10 L25588015069.8  L25676620350.2  L25858816235.5  L25952359058.3  L25984553605.8  L27848808849.2  L29461966392.2  L30035708878.6  L3030662567.2   L30449887874.5  L31797641758.132L31804147589.105L32075229189.0  L33945784403.3  L36262250517.7  L36438198037.7  L36841451887.5  L37682279081.10 L37685743390.3  L37888894965.7  L38235734261.1  L38637156310.6  L39831478948.2  L407260245.7    L41699122995.7  L42155231742.3  L42629649926.2  L45450656780.1  L46046034755.7  L46047259582.2  L46156896021.7  L46336856945.9  L47868035168.8  L48562303429.8  L48691446163.7  L48711619285.7  L48955120189.3  L5036908905.138 L50974193924.5  L528673413.7    L53271059539.7  L5429770831.4   L55123201336.2  L55125122501.7  L5780586706.7   L583080789.7    L59520256275.7  L60805037525.2  L61031298631.9  L61538482259.3  L61929720224.2  L62835699605.7  L62984661301.7  L645647890.2    L65092451413.7  L65104223396.2  L66006464133.8  L66240431488.7  L66568461826.7  L67046461077.7  L67446014369.0  L68231271950.10 L6902520326.132 L6904438685.105 L8806423751.6   L8873338536.3   L9265737838.6   00000>00L00[00f01301:01E01T01_01j02@02S02f03403G03U03g04A04V04]05705;05C05Q05X05k06606@06G06N06h06o07E07[07i07j08508=08E08R09709G09a09e0:90:C0:K0:e0;30;;0;?0;J0;Q0;Y0<30<V0<h0=00=80=C0=Y0=n0>90>A0>J0>Q0>\0?50?=0?E0?M0?U0?`0?f0?n0@H0@L0@T0@^0A00AJ0A`0Ah0Ai0B60BL0BZ0Bl0C70CPS3hAR2SP2ws2HLS3hAR2SP2ws2HLS2SP3TOP1x2Hx1HS2SP2lo3TOPS2SP2lo1A1k1HS2SP2loS3hAR2SP2loS3TOP4TOP04TOP1S3hAR2SP2loS2SP3TOP2GTS3hAR2SP2lo1T2T15LOIMGS3hAR2lo1T2T15LOIMGS3hAR2lo1T2T15LOIMGS3hAR2SP2ws2HLS2SP2lo4TOPU2a'3Ha'S2SP2lo1T1x2HxS2SP2lo3SPL1A1k2H1S3hAR2SP2lo1T2T15LOIMG3SPLS3hAR2SP2lo5LOIMG3SPLS2SP2loS3hAR2SP2lo1T2T15LOIMG3SPLS2SPS3hAR2SPS2SP2lo1A1k2H1S2SP2loS3hAR2lo1T2T15LOIMGS2SP2lo3TOPS1T1A1k2H2S2SP2loS2SP2loS3hAR2SP2lo4TOP25LOIMG3SPLS2SP2loS3hAR2lo3CTX3CX15LOIMGS3hAR2SP2ws2HL3ws23HL2S3hAR2SP2ws2HLSS2SP2lo3SPLS3hAR2SPS3hAR2SPS2SP2lo1A1k1HS3hAR2SP2lo1T3CTX3TOP2T13CX12TC5LOIMGS3TOP4TOPU5TOPUBS3hAR2SP2lo1T2T15LOIMG3SPLS2loS3hAR2lo5LOIMG1A1k1HS4size3SZBS3hAR2SPS3hAR2SP2lo1T2T15LOIMG3SPLS3hAR2lo5LOIMGS2SP3SPHS2SPS3hAR2SP2loS2SP2loS3hAR2SPS3hAR2SP2lo4TOP25LOIMG3SPLS3hAR2SP2lo3TOP4TOP14TOP25LOIMG3SPLS2SP2lo3SPL1A1k2H1S3hAR2SPS3hAR2SPS2SP3TOP2LES3hAR2SP2ws2HL3ws23HL2S3hAR2SP2lo5LOIMG3SPLS3hAR2SP2loS3hAR2SPS2SP4TOP2S2SP2loS3hAR2SP2loS3hAR1T3CTX2T02T13CX03CX1S3hAR2SPS3hAR2SPS2SP3TOPS3hAR2SPS2SP2lo3SPLS1n2NBS3hAR2SPS3hAR2SP2lo1T2T15LOIMG3SPLS2SPS3hAR2SPS4size3SZBS2SP2lo3SPL1A1k2H1S3hAR2SP2lo1T2T15LOIMG3SPLS2SP2lo3TOP3SPL1x2Hx1HS3hAR2SPSS3hAR2SP1q2HqS3hAR2SP2ws2HL3ws23HL2S3hAR2SP2ws2HLS2SP2lo1T3SPL1x2HxS2SP2lo3SPLS3hAR2SP2lo5LOIMG3SPL3SPH". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma msegA : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Pra,(13.&40.)Pgp,(13.&40.)Pt0,(13.&40.)Pt1,(13.&40.)Pt2,(13.&40.)Ps0,(13.&40.)Ps1,(13.&40.)Pa1,(13.&40.)Pa2,(13.&40.)Pa3,(13.&40.)Pa4,(13.&40.)Pa5,(13.&40.)Pa6,(13.&40.)Pa7,(13.&40.)Ps2,(13.&40.)Ps3,(13.&40.)Ps4,(13.&40.)Ps5,(13.&40.)Ps6,(13.&40.)Ps7,(13.&40.)Ps8,(13.&40.)Ps9,(13.&40.)Ps10,(13.&40.)Ps11,(13.&40.)Pt3,(13.&40.)Pt4,(13.&40.)Pt5,(13.&40.)Pt6,(13.&40.)PSP,$1:.Pn,$1:.Plo,$1:.PT,$1:.PCTX,$1:.PTOP,$1:.PLO,$1:.PTOPU,$1:.Pd,$1:.PF,(36.&5.(13.&40.))Pfc,(13.&20.)Pm,P,(13.&40.)(19.(13.&8.))P,(0.(1=.=R;.)(37.R;.(38.+2.+20.)))P,(39.$2.R2.R7.R6.(3:.&40.R24.)R=.R5.)P,(1=.R8.R>.)P,(0.(1=.R:.R8.)(1=.R8.(38.+2.+40.)))P,(1;.R5.R=.R<.)P,(1.$2.R6.(16.R>.+8.)(4.$5.(<.(7.&40.R<.))(4.$5.(<.(7.&40.(3;.R<.(38.+2.+17.))))(8.$5.))))P,(1.$2.R7.(16.R?.+28.)(4.$5.(6.(7.&8.=))(8.$5.)))P,(30.$2.R8.(16.R10.+<60.)(4.$5.(6.(7.&8.=))(8.$5.)))P,(1=.(38.+2.+17.)R?.)P,(1=.R10.(38.+2.+2?.))P,(1=.(16.R16.+10.)(38.+2.+2?.))P,(0.(1=.+1000.R14.)(3<.(1=.(16.R14.+1000.)+10000.)(1=.+65?000.R14.)))P,(1=.(16.R15.+1000.)(3=.VhAR,))P,(1=.+65?000.R15.)P,(1=.(16.R16.+10000.)(3=.VhAR,))P,(3<.(1=.(16.R18.+1000.)R17.)(1=.(16.R17.+10000.)R18.))P,(3>.VCS,R19.+1000.)P,(3>.VCS,R19.+10000.)P,(34.$2.R13.R1>.R19.)P,(3>.VCS,R1?.(3;.R1:.R1?.))P,(34.$2.R15.R1>.R20.)P,(1=.(3=.VhAR,)R1?.)P,(1=.R20.(3;.R22.+1000.))P,(23.$1:.(3?.R23.+10.)=)P,(3>.VCS,R22.(3;.R24.R22.))P,(2?.$2.R1:.)(40.$2.VAL,VCS,(41.R26.R41.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R42.R3=.R3<.R1=.R1<.R25.R24.R23.R21.R1>.R1;.)(24.(25.R42.(7.&40.R26.)R41.(7.&40.$26.)R40.R3?.R3>.R3=.R3<.(7.&40.R25.)R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)R1=.(7.&40.$42.)R1<.(2:.(13.&40.))R1;.(2;.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP n lo T CTX TOP LO TOPU d F fc m
      NB CH0 LOB TOPUB MS8 THR TSW UNW TOP0 TOP1 TOP2 T0 T1 CX0 CX1 TC TCS CTXCS STT STCS ST LOIMG SPL SPA SCS MI.
    pose proof (u64_range s0) as S0R.
    facts. dpose MS8 as (INI & MCS & GOTF & FU & GOT & PGS & TSD & TPC & TSA & CTH).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (malloc_pro AL IMG ALWF CS CSOK); try eassumption. clear - NB; lia. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (m1 & ws & fr1 & fr2 & -> & MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL & F1800 & TFB & F8 & ST1)).
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
    pose proof (proj1 (rw_cells_app asegs m1 (SP + -2128) [C8 _] _) STKC) as [SK0 SK1]. cbn [cells_size csize Nat.add] in SK1.
    pose proof (proj1 (rw_cells_app asegs m1 _ [C4 _] _) SK1) as [SK8 SK12]. cbn [cells_size csize Nat.add] in SK12. clear STKC SK1.
    replace (SP + -2128 + Z.of_nat 8) with (SP + -2128 + 8) in SK8 by lia. replace (SP + -2128 + Z.of_nat 8 + Z.of_nat 4) with (SP + -2128 + 12) in SK12 by lia.
    (* [comment removed for export] *)
    assert (STT1' : stk asegs m1 SP (Z.max TOP SP)).
    { destruct (Z.le_gt_cases SP TOP) as [LE|GT]; [rewrite Z.max_l by (clear - LE; lia); exact STT1| rewrite Z.max_r by (clear - GT; lia); apply stk_empty; clear - TOP2 LOIMG SPL; lia]. }
    assert (SR1 : stk asegs m1 (SP + -16) (Z.max TOP SP)).
    { eapply stk_merge; [| exact STT1'| clear; lia].
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FR7) as [_ FRhi].
      cbn [cells_size csize Nat.add] in FRhi. replace (SP + -56 + Z.of_nat 40) with (SP + -16) in FRhi by lia.
      pose proof (stk_of_rw_cells asegs m1 (SP + -16) _ FRhi) as X. cbn [cells_size csize Nat.add] in X.
      replace (SP + -16 + Z.of_nat 16) with SP in X by lia. exact X. }
    (* [comment removed for export] *)
    assert (LNK1 : ro_cells asegs m1 (SP + -16) [C8 (Z_to_bv 64 (bv_unsigned s0))]).
    { rewrite Z_to_bv_bv_unsigned.
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) FR7) as [_ FRhi].
      cbn [cells_size csize Nat.add] in FRhi. replace (SP + -56 + Z.of_nat 40) with (SP + -16) in FRhi by lia.
      pose proof (proj1 (rw_cells_app asegs m1 (SP + -16) [C8 s0] [C8 ra]) FRhi) as [[X _] _]. exact X. }
    assert (CH1 : uwc asegs m1 LO TOPU (bv_unsigned s0) SP d).
    { eapply (uwc_munch asegs [(lo, SP)]); [exact CH0| exact MU1| clear - LOIMG SPL; lia| clear - TOPUB; lia| intros a' Ha'; cbn; clear - Ha'; lia]. }
    clear CH0.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (unwind_impl_spec AL IMG ALWF CS CSOK (SP + -2128) A_PC_MALLOC SP TOP (TOP - 2^23) (SP + -16) (Z.max TOP SP) T CTX) with (LO := LO) (TOPU := TOPU);
        [ | | | | | | | | | | | exact LOB | exact TOPUB | clear - T1 LOIMG SPL; lia | exact HL | exact SK8 | exact HTR | exact TFB | exact SR1 | exact LNK1 | exact CH1 | exact S0R | exact GOT1 | exact PGS1 | exact INI1 | exact TSD1 | exact TPC1 | exact TSA1 | exact CTH1 | exact THR1 | exact TSW1 | exact UNW1 | exact ST1 | clear - LOIMG; lia | clear - SPL; lia | clear; lia | | exact MI1 | reflexivity ].
      - clear - TOP2 TOP1 LOIMG SPL. lia.
      - intros x Hx. destruct (Z.lt_ge_cases x SP); [apply SCS; clear - Hx H SPL; lia| apply STCS; clear - Hx H; lia].
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear - SPL; lia| clear; lia].
      - clear - LOIMG SPL; lia.
      - clear - TOP0 TOP1; lia.
      - unfold A_PC_MALLOC. clear; lia.
      - clear - TOP1 TOP2 LOIMG SPL SPA. split; [lia|]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in SPA; [|lia]. destruct SPA as [q Hq]. exists (2 * q). lia.
      - exact TCS. - exact CTXCS.
      - clear - T0 T1 CX0 CX1. lia.
      - clear - T1 CX1 TC LOIMG. lia.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
    cbn beta. (intros ms2 dd_H; ddestruct dd_H as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ws2 & size & -> &
                          MU2 & WM2 & MI2 & SZ2 & HTR2 & TFB2 & UNW2 & SZB & SZD & HL2 & ST2 & SR2)).
    replace (ret_pc (Z_to_bv 64 0x6977c)) with (Z_to_bv 64 0x6977c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    zstep. zstep. replace (SP + -2048 + -80) with (SP + -2128) by lia. zstep. zstep.
    (* [comment removed for export] *)
    assert (DJ2 : forall A k, (A + k <= lo \/ SP + -2128 + 2064 <= A) -> (A + k <= T + 3168 \/ T + 3169 <= A) ->
              disjoint_from [(SP + -2128 + 8, SP + -2128 + 12); (SP + -2128 + 16, SP + -2128 + 256); (SP + -2128 + 2056, SP + -2128 + 2064); (T + 3168, T + 3169); (lo, SP + -2128)] A k).
    { intros A k H1 H2. cbn [disjoint_from]. clear - H1 H2 SPL. repeat split; lia. }
    assert (FR7' : rw_cells asegs m2 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR7| exact MU2| exact WM2| apply DJ2; cbn; clear - T1 LOIMG SPL; lia]).
    assert (SK0' : rw_cells asegs m2 (SP + -2128) [C8 (Z_to_bv 64 (SP + -2128 + 16))]).
    { eapply rw_cells_transport; [exact SK0| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL T1 LOIMG. repeat split; lia. }
    assert (SK12' : rw_cells asegs m2 (SP + -2128 + 12) [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact SK12| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. clear - SPL T1 LOIMG. repeat split; lia. }
    assert (F1800' : rw_cells asegs m2 (SP + -2128 + 256) [CB 1800 fr1])
      by (eapply rw_cells_transport; [exact F1800| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    assert (F8' : rw_cells asegs m2 (SP + -2128 + 2064) [CB 8 fr2])
      by (eapply rw_cells_transport; [exact F8| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - SPL T1 LOIMG; repeat split; lia]).
    clear FR7 SK0 SK12 F1800 F8 SK8 HTR TFB SR1 STT1 ST1 UNW1.
    (* [comment removed for export] *)
    assert (STKC : rw_cells asegs m2 (SP + -2128) [C8 (Z_to_bv 64 (SP + -2128 + 16)); C8 (Z_to_bv 64 size)]).
    { apply (proj2 (rw_cells_app asegs m2 (SP + -2128) [C8 _] [C8 _])). split; [exact SK0'|]. cbn [cells_size csize Nat.add].
      eapply (rw_cells_reshape asegs m2 _ [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 0)]).
      - apply (proj2 (rw_cells_app asegs m2 _ [C4 _] [C4 _])). split; [replace (SP + -2128 + Z.of_nat 8) with (SP + -2128 + 8) by lia; exact SZ2|].
        cbn [cells_size csize Nat.add]. replace (SP + -2128 + Z.of_nat 8 + Z.of_nat 4) with (SP + -2128 + 12) by lia. exact SK12'.
      - cbn. tauto.
      - cbn [cells_bytes cbytes]. rewrite (le8_split4 (Z_to_bv 64 size)). rewrite unsigned_lit by (clear - SZB; lia).
        rewrite Z.div_small by (clear - SZB; lia). rewrite <- app_assoc. reflexivity. }
    clear SK0' SK12' SZ2.
    (* [comment removed for export] *)
    eapply evtA_mono.
    { eapply (amalloc_pro AL IMG ALWF CS CSOK); [clear - NB; lia| clear - SPL LOIMG SPH; lia| exact ST2| exact LOIMG| clear - SPL; lia| clear - SPH; lia| | | exact MI2].
      - clear - SPA. replace (SP + -2128) with (SP + (-133) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| clear; lia]. }
    cbn beta. (intros ms3 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & AFR & ST3)).
    unfold segA_post. deexists 9. dexists m3, ws2, size, fr1, fr2.
    split; [reflexivity|].
    assert (LO3 : forall A k, (A + k <= lo \/ SP + -2128 <= A) -> disjoint_from [(lo, SP + -2128)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
    split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
             eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. clear - SPL. intros x Hx. lia. }
             eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear - SPL. intros x Hx. lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|].
    split; [eapply rw_cells_transport; [exact FR7'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact STKC| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply u64arr_transport; [exact HTR2| exact MU3| exact WM3| apply LO3; rewrite HL2; cbn; clear; lia]|].
    split; [exact HL2|]. split; [exact SZB|]. split; [exact SZD|].
    split; [eapply rw_cells_transport; [exact F1800'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact TFB2| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact F8'| exact MU3| exact WM3| apply LO3; cbn; clear; lia]|].
    split; [exact AFR|].
    split; [eapply rw_cells_transport; [exact UNW2| exact MU3| exact WM3| apply LO3; cbn; clear - T1 LOIMG; lia]|].
    split; [exact ST3|].
    eapply stk_transport_disjoint; [exact SR2| exact MU3| exact WM3| apply LO3; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section SegB.
    Variables (SP n lo T CTX TID SB cnt csz : Z) (pw : word).
    Let STK := SP + -2128.
    Let SPA := SP + -2128 + -16.            (* [comment removed for export] *)
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

    Definition segB_post (gp : word) (F : bvmap 5 word) (fc : bv 32) (size : Z) (CS' : Z -> Prop)
        (q6 q7 q8 q9 q10 q11 mx : word) (ws16 : list word) (b0 : byte) (w8 : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Lms',$21.(22.(13.&40.)Lx5,(13.&40.)(22.(13.&40.)Lx6,(13.&40.)(22.(13.&40.)Lx7,(13.&40.)(22.(13.&40.)Lx12,(13.&40.)(22.(13.&40.)Lx13,(13.&40.)(22.(13.&40.)Lx14,(13.&40.)(22.(13.&40.)Lx15,(13.&40.)(22.(13.&40.)Lx16,(13.&40.)(22.(13.&40.)Lx17,(13.&40.)(22.(13.&40.)Lt3,(13.&40.)(22.(13.&40.)Lt4,(13.&40.)(22.(13.&40.)Lt5,(13.&40.)(22.(13.&40.)Lt6,(13.&40.)(22.$1:.Lb1,$1:.(22.(13.&40.)Lstw',(13.&40.)(22.(17.(13.&8.))Lfr0,(17.(13.&8.))(22.P,(13.&40.)(19.(13.&8.))Lm',P,(13.&40.)(19.(13.&8.))(0.(23.$21.R12.(24.(25.(7.&40.+47>40.)(7.&40.(16.VSPA,-80.))O10.(7.&40.$26.)R11.R10.R?.(7.&40.+1.)(7.&40.(43.Vn,))(7.&40.(16.VSTK,+10.))(7.&40.O=.)R>.R=.R<.R;.R:.R9.(7.&40.VAB,)(7.&40.(44.Vn,))(7.&40.VUB,)(7.&40.VCHB,)(7.&40.$27.)(7.&40.VSTK,)(7.&40.(45.VTID,(38.+2.+20.)))(7.&40.(16.VUB,(43.Vn,)))(7.&40.VT,)(7.&40.+1.)R8.R7.R6.R5.)O?.(7.&40.$46.)O>.(2:.(13.&40.))R1.(2;.$2.)))(0.(1<.(4.(2<.$1:.$1:.)(2=.$1:.$1:.Vlo,VSPA,)(4.(2<.$1:.$1:.)(2=.$1:.$1:.(16.(16.VT,+=0.)(45.+50.Vc,))(16.(16.(16.VT,+=0.)(45.+50.Vc,))+4.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.(16.VT,+:>0.)(16.VT,+:>8.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.VCHB,(16.VCHB,+8.))(8.(2<.$1:.$1:.))))))O1.R1.)(0.(2>.$2.O1.R1.)(0.(2?.$2.R1.)(0.(30.$2.R1.VCHB,(4.$5.(6.O3.)(4.$5.(6.(7.&8.R4.))(4.$5.(47.(7.&40.=))(4.$5.(:.(7.&40.(43.Vn,)))(4.$5.(<.O2.)(8.$5.)))))))(0.(23.$1:.(48.R4.+3.)+1.)(0.(0.(1=.=R4.)(37.R4.+100.))(0.(49.R1.VSPA,R2.+1.(7.&40.+47:64.)(7.&40.VSP,)(7.&40.Vn,)(7.&40.$28.)(7.&40.+1.)(7.&40.VSTK,)(7.&40.(16.VSP,-51.))O;.O:.O9.O8.O7.O6.)(0.(30.$2.R1.(16.(16.VT,+=0.)(45.+50.Vc,))(4.$5.(:.(7.&40.(3;.Vcnt,+1.)))(4.$5.(:.O5.)(4.$5.(<.(7.&40.Vcsz,))(8.$5.)))))(0.(4:.$2.R1.(16.(16.(16.VT,+=0.)(45.+50.Vc,))+10.)O4.)(0.(30.$2.R1.(16.VT,+:>0.)(4.$5.(<.R3.)(8.$5.)))(34.$2.R1.Vlo,(16.VSPA,-80.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "01<0@L10048915757.10 L10069906815.15 L10497895552.4  L12104406627.2  L12582944717.8  L13680019589.10 L13885224728.7  L15527186106.6  L16840733163.10 L18982057934.2  L19463478621.9  L19467640919.15 L19782509618.5  L20554108099.9  L20558344649.15 L20709543634.11 L20957647993.4  L2261078798.7   L22706556809.5  L22991948770.9  L23873806138.9  L2420374951.2   L24472997875.14 L24670452403.10 L24881781866.7  L24888640626.2  L24897143244.3  L2513005359.3   L26069506564.16 L27697017043.3  L27848808849.2  L28280009621.14 L28934870315.6  L32382492013.2  L33896187502.8  L34239203029.5  L34961556125.10 L35241383781.11 L35247679960.8  L35360265620.12 L35585147581.10 L36154435895.13 L3661429958.2   L36841451887.6  L37300721413.15 L37302917044.7  L3813344308.4   L38235734261.1  L40821008992.6  L41596053439.3  L42333736697.5  L44340933537.15 L50071402333.15 L52016747867.7  L53285612562.8  L54570223649.3  L5631637877.10  L56750996366.2  L56829362200.11 L58913627406.0  L61030955888.165L63374621462.166L63433282004.8  L63469717261.6  L63737759283.1  L65599540417.7  L66623653861.10 L67172748439.3  L67645412041.5  L8201234081.0   L8759167375.5   L8873338536.3   L9265737838.6   L9714519104.6   L9818858585.12  L9871287523.10  00000?00g01701?01Z02802U02n03@03G03e04I04^05<05`06506E06b07207Q07n08508Y09:09P09T09X09e0:O0:Z0:a0;B0;T0;\0;g0<:0<X0<n0=I0=j0>H0?20?60?G0?h0@B0@E0@I0@Z0@e0A50A]0BB0B_0C90CD0CS0CW0Cl0Cm0D`0ES0Ea0F30F70FQ0Ff0G00G80G90GN0GY0H20HE0Ho0IPS3hAR2SP1n2lo1cS3hAR2SP1n1T2SB2pw3SPA1c3ABT4RZSB2CR3N2BS2SP2lo3SPA4SPALS2SP3SPHS3hAR2SP2lo3SPA5LOIMG1A1k1HS3hAR2SP1n2lo1T1c5LOIMG3SPL2T1S3hAR2SP2lo3CTX3SPA5LOIMG3CX1S3hAR2SP2lo5LOIMG3SPL3SPHS3hAR1n1T3CTX1c2TCS2SP2loS3hAR2SP1n2lo1T3SPA5LOIMG2T11HS3hAR2SP1n2lo1T2pw3SPA1c5LOIMG2T12CRS3hAR2SP2lo3SPA5LOIMGS3hAR2SP1n2lo1T3SPA5LOIMG2T11HS3hAR2SP1n2lo1T2pw3SPA1c5LOIMG2T12CRS2SP1n1T3SPA1c1A1k2H3S2SP2lo3SPA4SPALS3hAR2SP2lo3CTX3SPA5LOIMG3CX1S2SP2lo3SPA1x2HxS1n3CTX2SB2pw1c2AB3ABC4RZSB3N2BS1n1T2SB2pw1c2AB3ABT4RZSB3N2BS2SP2loS3hAR1n1T2SB2pw1c2AB3ABT4RZSB2CR3N2BS3hAR2SP1n2lo1T1c5LOIMG3SPL2T12CRS3hAR1n2SB2pw1c2AB3AB1S2SPS2SPS2SP3SPA4SPAHS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB13N2BS1n3N2E3NDBS2SP2loS3hAR1n1T2SB2pw1c2AB3ABT4RZSB3N2BS1n2SB2pw1c2AB3N2BS2SP3SPHS3hAR1n1T1cS3hAR2lo1T5LOIMG2T1S3hAR2SP1n2lo1T3SPA1c5LOIMG2T1S2SP1n2lo3SPA1c1A1k2H1S3hAR2SP2lo3SPA5LOIMG1A1k1HS3hAR2SP1n2lo3CTX3SPA1c5LOIMG3CX1S3hAR2SP1n2lo1T1c5LOIMG3SPL2T1S3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB13N2BS2SPS2SP2lo3SPA1A1k1HS3hAR2SP1n2lo1T2pw3SPA1c5LOIMG2T1S3hAR2SP2lo1T3SPA5LOIMG2T1S1qS2loS2SP2lo3SPA1A1k1HS2SP2lo3SPAS2SP2lo3SPA1x2H1S3hAR2SP1n1T2SB2pw3SPA1c3ABT4RZSB2CR3N2BS3hAR2SP1n1T2SB2pw3SPA1c3ABT4RZSB3N2BS3hAR2SP2lo3CTX3SPA5LOIMG3CX1S3hAR1n2SB2pw1c2AB3AB13N2BS2SP2lo3SPLS3hAR2SP1n2lo1cS2SPS2SP1n1T3SPA1c1A1k2H2SS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB04ws163LWSS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB04ws163LWSS3hAR1n1T1c2CRS1n2SB2pw1c2AB3AB0S2SPS3hAR2SP2lo1T3SPA5LOIMG2T1S3hAR1n1T3CTX1c2TC2CRS3hAR1T2T1S1n1H2H0SS3hAR2SP2lo5LOIMG3SPLS2SP2lo3SPLS3hAR2SP2lo5LOIMG3SPL3SPHS1n2SB2pw1c2AB4RZSBS3hAR2SP1n2lo2SB2pw1c2AB5LOIMG3SPL3AB13N2BS3hAR2SP1n2lo1T1c5LOIMG3SPL2T12CR". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK NB FP LOIMG SPL SPH SPA16 T0 T1 TAL CX0 CX1 TC TIDB SB0 SB1 SBAL HCNT HCSZ AB0 AB1 ABT ABC"] Lemma msegB : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Pgp,(13.&40.)Pt0,(13.&40.)Pt1,(13.&40.)Pt2,(13.&40.)Pa6,(13.&40.)Pa7,(13.&40.)Pq6,(13.&40.)Pq7,(13.&40.)Pq8,(13.&40.)Pq9,(13.&40.)Pq10,(13.&40.)Pq11,(13.&40.)Pt3,(13.&40.)Pt4,(13.&40.)Pt5,(13.&40.)Pt6,(13.&40.)Pmx,(13.&40.)Pstw,(13.&40.)Pb0,(13.&8.)Pb1,(13.&8.)Pw2,(13.&40.)Pw4,(13.&40.)Pw8,(13.&40.)PF,(36.&5.(13.&40.))Pfc,(13.&20.)Pm,P,(13.&40.)(19.(13.&8.))Psize,$1:.Pws16,(17.(13.&40.))P,(1?.R3.VT,VCTX,)P,(3>.VCS,VT,+1000.)P,(3>.VCS,VCTX,+10000.)P,(0.(1=.=R5.)(37.R5.(38.+2.+20.)))P,(23.$32.(33.(13.&40.)R5.)#10.)P,(23.(19.(13.&40.))(4;.(13.&40.)R6.(4<.(3;.Vcnt,+1.)))(4=.(13.&40.)Vpw,))P,(1.$2.R9.(16.$27.+20.)(4.$5.(<.(7.&40.VSB,))(8.$5.)))P,(30.$2.R:.(16.(16.VT,+=0.)(45.+50.Vc,))(4.$5.(:.(7.&40.Vcnt,))(4.$5.(:.R13.)(4.$5.(<.(7.&40.Vcsz,))(8.$5.)))))P,(4:.$2.R;.(16.(16.(16.VT,+=0.)(45.+50.Vc,))+10.)R9.)P,(30.$2.R<.(16.VT,+:>0.)(4.$5.(<.R14.)(8.$5.)))P,(3>.VCS,VAB,(44.Vn,))P,(30.$2.R>.VCHB,(4.$5.(6.R15.)(4.$5.(6.R14.)(4.$5.(47.R13.)(4.$5.(:.R12.)(4.$5.(<.R11.)(8.$5.)))))))P,(1.$2.R?.VT,(4.$5.(<.(7.&40.VCTX,))(8.$5.)))P,(1.$2.R10.(16.VCTX,+8.)(4.$5.(:.(7.&40.VTID,))(8.$5.)))P,(30.$2.R11.VSTK,(4.$5.(<.(7.&40.(16.VSTK,+10.)))(4.$5.(<.(7.&40.R10.))(8.$5.))))P,(34.$2.R12.Vlo,VSPA,)P,(3>.VCS,Vlo,(3;.VSP,Vlo,))P,(2?.$2.R14.)(40.$2.VAL,VCS,(4>.R2>.R17.R16.R14.VCS,R28.R27.R26.R25.R24.R23.R1>.R13.R1<.R18.R15.)(24.(25.(7.&40.+47:64.)(7.&40.VSPA,)R2>.(7.&40.$26.)R2=.R2<.R2;.(7.&40.VSP,)(7.&40.Vn,)(7.&40.$27.)(7.&40.Vn,)(7.&40.+8.)(7.&40.VSTK,)(7.&40.+1.)(7.&40.+1.)R2:.R29.(7.&40.$28.)(7.&40.+1.)(7.&40.VSTK,)(7.&40.(16.VSP,-51.))R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R17.(7.&40.$29.)R16.(2:.(13.&40.))R15.(2;.$2.)))")
(* [comment removed for export] *).
    Proof.
      intros gp t0 t1 t2 a6 a7 q6 q7 q8 q9 q10 q11 t3 t4 t5 t6 mx stw b0 b1 w2 w4 w8 F fc m size ws16
        AS TCS CTXCS SZB LWS NTH SBC PC ARR STC ACS HDR TH TIDC STKC ST SCS MI.
      facts. pose proof needed2_primary as [N2E NDB]. pose proof AB_al as ABAL. pose proof (rz_size_bound n) as RZSB.
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2128 + -16) with (SP + (-134) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (STKB : 0 < STK < 2^64) by (subst STK; clear - SPL LOIMG SPH; lia).
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_proA AL IMG ALWF CS CSOK); [exact NB| exact STKB| clear; lia| exact AS| exact ST| exact LOIMG| clear - SPAL; lia| exact SPAH| exact SPAAL| exact SCSA| exact MI]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x10 & x11 & x12 & x13 & m1 & fr0 & -> & MU1 & WM1 & MI1 & FR1 & ST1)).
      assert (LO1 : forall A k, (A + k <= lo \/ SPA <= A) -> disjoint_from [(lo, SPA)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
      assert (AS1 : allocA_statics m1 T CTX) by (eapply (allocA_statics_transport _ m m1 T CTX AS MU1); [intros A k H; apply LO1; clear - H LOIMG; lia| apply LO1; clear - CX1 LOIMG; lia]).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_proB AL IMG ALWF CS CSOK) with (W := []); [exact NB| exact AS1| exact ST1| exact LOIMG| exact SPAL| exact SPAH| exact SPAAL| exact SCSA| apply munch_refl| apply wmono_refl| exact MI1]. }
      cbn beta. (intros ms2 dd_H; ddestruct dd_H as (m2 & PB & MU2 & WM2 & MI2 & MU2' & ST2)). ddestruct PB as (y11 & y12 & y13 & y14 & ->).
      assert (LO2 : forall A k, (A + k <= lo \/ SPA + -128 <= A) -> disjoint_from [(lo, SPA + -128)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
      assert (AS2 : allocA_statics m2 T CTX) by (eapply (allocA_statics_transport _ m1 m2 T CTX AS1 MU2'); [intros A k H; apply LO2; clear - H LOIMG; lia| apply LO2; clear - CX1 LOIMG; lia]).
      eapply evtA_cut.
      { eapply (alloc_proC AL IMG ALWF CS CSOK) with (W := []); [exact NB| exact AS2| exact CX0| exact CX1| exact T0| exact T1| exact CTXCS| exact TCS| exact ST2| exact LOIMG| exact SPAL| exact SPAH| exact SPAAL| exact SCSA| apply munch_refl| apply wmono_refl| exact MI2| reflexivity]. }
      cbn beta. (intros ms3 dd_H; ddestruct dd_H as (m3 & PCp & MU3 & WM3 & MI3 & MU3' & ST3)). ddestruct PCp as (z14 & z15 & z16 & z17 & ->).
      (* [comment removed for export] *)
      assert (MU03 : munch [(lo, SPA)] m m3).
      { eapply munch_trans; [exact MU1|]. eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
      assert (WM03 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
      assert (SBC3 : ro_cells asegs m3 (A_INSTANCE + 32) [C8 (Z_to_bv 64 SB)]) by (eapply ro_cells_transport; [exact SBC| exact MU03| apply LO1; unfold A_INSTANCE; cbn; clear - LOIMG; lia]).
      assert (PC3 : rw_cells asegs m3 (T + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 mx; C8 (Z_to_bv 64 csz)]).
      { eapply rw_cells_transport; [exact PC| exact MU03| exact WM03| apply LO1; cbn]. pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E; lia)). clear - T1 LOIMG H. subst c. lia. }
      assert (ARR3 : u32arr asegs m3 (T + 208 + 80 * c + 16) ws16).
      { eapply u32arr_transport; [exact ARR| exact MU03| exact WM03| apply LO1; rewrite LWS; cbn]. pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E; lia)). clear - T1 LOIMG H. subst c. lia. }
      assert (STC3 : rw_cells asegs m3 (T + 2784) [C8 stw]) by (eapply rw_cells_transport; [exact STC| exact MU03| exact WM03| apply LO1; cbn; clear - T1 LOIMG; lia]).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (comb_hit_spec AL IMG ALWF CS CSOK) with (x := needed2 n) (cnt := cnt);
          [ clear - NDB N2E; lia | exact T0 | clear - T1; lia | exact TAL | exact TCS | exact SB0 | exact SB1 | exact HCNT | exact HCSZ | exact LWS | exact NTH
          | exact SBC3 | exact PC3 | exact ARR3 | exact STC3 | exact ST3 | exact LOIMG | clear - SPAL; lia | clear - SPAH; lia | | left; clear - T1 LOIMG; lia | | exact MI3 ].
        - subst SPA. clear - SPA16. replace (SP + -2128 + -16 + -128) with (SP + (-142) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16.
        - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]. }
      cbn beta. (intros ms4 dd_H; ddestruct dd_H as (w5 & w6 & w11 & w12 & w14 & w15 & w16 & w17 & m4 & stw' & -> & MU4 & WM4 & MI4 & PC4 & ARR4 & STC4 & ST4)).
      replace (ret_pc (Z_to_bv 64 0x47d34)) with (Z_to_bv 64 0x47d34) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      fold AB.
      pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E; lia)) as CR. fold c in CR.
      assert (DJ4 : forall A k, (A + k <= lo \/ SPA + -128 <= A) -> (A + k <= T + 208 + 80 * c \/ T + 208 + 80 * c + 4 <= A) -> (A + k <= T + 2784 \/ T + 2792 <= A) ->
               disjoint_from [(lo, SPA + -128); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2792)] A k).
      { intros A k H1 H2 H3. cbn [disjoint_from]. clear - H1 H2 H3. repeat split; lia. }
      assert (N2B : rz_size n + 8 <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 NB RZSB; lia. }
      assert (HDR4 : rw_cells asegs m4 CHB [C1 b0; C1 b1; C2 w2; C4 w4; C8 w8]).
      { eapply rw_cells_transport; [| exact MU4| exact WM4|].
        { eapply rw_cells_transport; [exact HDR| exact MU03| exact WM03| apply LO1; cbn; subst CHB; clear - AB1 LOIMG N2B RZSB; lia]. }
        apply DJ4; cbn; subst CHB; clear - AB1 LOIMG N2B RZSB ABT CR; lia. }
      assert (TH4 : ro_cells asegs m4 T [C8 (Z_to_bv 64 CTX)]).
      { eapply ro_cells_transport; [| exact MU4|]. { eapply ro_cells_transport; [exact TH| exact MU03| apply LO1; cbn; clear - T1 LOIMG; lia]. } apply DJ4; cbn; clear - T1 LOIMG CR; lia. }
      assert (TIDC4 : ro_cells asegs m4 (CTX + 8) [C4 (Z_to_bv 64 TID)]).
      { eapply ro_cells_transport; [| exact MU4|]. { eapply ro_cells_transport; [exact TIDC| exact MU03| apply LO1; cbn; clear - CX1 LOIMG; lia]. } apply DJ4; cbn; clear - CX1 LOIMG TC CR; lia. }
      assert (STKC4 : ro_cells asegs m4 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]).
      { destruct STKC as [STKC0 _]. eapply ro_cells_transport; [| exact MU4|]. { eapply ro_cells_transport; [exact STKC0| exact MU03| apply LO1; cbn; subst STK SPA; clear; lia]. }
        apply DJ4; cbn; subst STK SPA; clear - T1 LOIMG SPL CR; lia. }
      assert (FR4 : allocA_frame m4 SPA fr0 1 (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) q6 q7 q8 q9 q10 q11).
      { unfold allocA_frame in *. eapply rw_cells_transport; [| exact MU4| exact WM4|].
        { eapply rw_cells_transport; [exact FR1| eapply munch_trans; [exact MU2'| exact MU3']| eapply wmono_trans; [exact WM2| exact WM3]|].
          cbn [disjoint_from cells_size csize Nat.add]. clear. lia. }
        apply DJ4; cbn; subst SPA; clear - T1 LOIMG SPL CR; lia. }
      (* [comment removed for export] *)
      eapply evtA_mono.
      { eapply (alloc_hdr AL IMG ALWF CS CSOK) with (W := @nil (Z * Z)) (TR := STK + 16) (size := size) (TID := TID) (CTX := CTX) (T := T) (lo := lo) (fill := 1);
          [ exact NB | clear - AB0; lia | clear - AB1; lia | exact ABAL | subst STK; clear - SPL LOIMG SPH; lia | exact SZB | exact TIDB | clear; lia
          | subst STK; clear - SPL LOIMG; lia | subst STK SPA; clear; lia | subst STK; clear - SPH; lia | | 
          | exact T0 | exact T1 | exact TCS | exact CX0 | exact CX1 | exact CTXCS | | | | | 
          | exact FR4 | exact HDR4 | exact TH4 | exact TIDC4 | exact STKC4 | exact ST4 | exact LOIMG | clear - SPAL; lia | exact SPAH | exact SPAAL | exact SCSA | | | exact MI4 ].
        - subst STK. clear - SPA16. apply Z.mod_divide in SPA16; [|lia]. destruct SPA16 as [q Hq]. rewrite Hq.
          replace (q * 16 + -2128) with ((2 * q - 266) * 8) by lia. apply Z_mod_mult.
        - eapply (crange_sub CS lo (SP - lo)); [exact SCS| subst STK; clear - SPL; lia| subst STK; clear; lia].
        - fold c AB. eapply (crange_sub CS AB (needed2 n)); [exact ACS| clear - RZSB; lia| clear - N2B; lia].
        - fold c AB. left. subst STK. clear - AB1 N2B LOIMG SPL. lia.
        - fold c AB. clear - AB1 N2B. lia.
        - fold c AB. clear - ABT N2B RZSB. lia.
        - fold c AB. clear - ABC N2B RZSB. lia.
        - apply munch_refl.
        - apply wmono_refl. }
      cbn beta. (intros ms5 dd_H; ddestruct dd_H as (v5 & v6 & v7 & v12 & v13 & v14 & v15 & v16 & v17 & b1' & m5 & -> & MU5 & WM5 & MI5 & HDR5 & B1T & B1R & FR5 & ST5)).
      fold c AB in MU5, HDR5 |- *. fold UB in HDR5 |- *. fold CHB in MU5, HDR5 |- *.
      rewrite FP. change (Z.b2z true) with 1.
      unfold segB_post. deexists 13. exists b1'. eexists. dexists fr0, m5.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU03]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_trans. { eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]. clear. (intros x dd_H; ddestruct dd_H as (H1 & H2 & H3 & H4 & _)). repeat split; [clear - H1; lia| exact H2| exact H3]. }
               eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
      split; [eapply wmono_trans; [exact WM03| eapply wmono_trans; [exact WM4| exact WM5]]|]. split; [exact MI5|].
      split; [exact HDR5|]. split; [exact B1T|]. split; [exact B1R|]. split; [exact FR5|].
      split. { eapply rw_cells_transport; [exact PC4| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB AB. clear - T1 LOIMG CR ABT N2B RZSB. repeat split; lia. }
      split. { eapply u32arr_transport; [exact ARR4| exact MU5| exact WM5|]. rewrite LWS. cbn [disjoint_from]. subst CHB AB. clear - T1 LOIMG CR ABT N2B RZSB. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact STC4| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB AB. clear - T1 LOIMG CR ABT N2B RZSB. repeat split; lia. }
      exact ST5.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Let SUB := 0x7fff8000 + UB / 8.                                  (* [comment removed for export] *)
    Let PGS := 0x7fff8000 + Z.shiftr (UB + nfix n / 8 * 8) 3.         (* [comment removed for export] *)
    Let KF := Z.min (nfix n) 4096.                                    (* [comment removed for export] *)

    Definition segC1_post (gp : word) (F : bvmap 5 word) (fc : bv 32) (id : Z) (b0 : byte) (b1 : Z) (q6 q7 q8 q9 q10 q11 : word) (fr0 : list byte) (pgb : byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Lms',$21.(22.(13.&40.)Lx1,(13.&40.)(22.(13.&40.)Lx5,(13.&40.)(22.(13.&40.)Lx6,(13.&40.)(22.(13.&40.)Lx7,(13.&40.)(22.(13.&40.)Lx10,(13.&40.)(22.(13.&40.)Lx11,(13.&40.)(22.(13.&40.)Lx12,(13.&40.)(22.(13.&40.)Lx13,(13.&40.)(22.(13.&40.)Lx14,(13.&40.)(22.(13.&40.)Lx15,(13.&40.)(22.(13.&40.)Lx16,(13.&40.)(22.(13.&40.)Lx17,(13.&40.)(22.(13.&40.)Lx22,(13.&40.)(22.(13.&40.)Ly28,(13.&40.)(22.(13.&40.)Ly29,(13.&40.)(22.(13.&40.)Ly30,(13.&40.)(22.(13.&40.)Ly31,(13.&40.)(22.(13.&40.)Lj0,(13.&40.)(22.(13.&40.)Lj1,(13.&40.)(22.(13.&40.)Lj2,(13.&40.)(22.(17.(13.&40.))Lbs,(17.(13.&40.))(22.P,(13.&40.)(19.(13.&8.))Lm',P,(13.&40.)(19.(13.&8.))(0.(23.$21.R17.(24.(25.R16.(7.&40.(16.VSPA,-80.))O?.(7.&40.$26.)R15.R14.R13.(7.&40.+1.)(7.&40.(43.Vn,))R12.R11.R10.R?.R>.R=.R<.R;.(7.&40.VAB,)(7.&40.(44.Vn,))(7.&40.VUB,)(7.&40.VCHB,)R:.(7.&40.VSTK,)(7.&40.(45.VTID,(38.+2.+20.)))(7.&40.(16.VUB,(43.Vn,)))(7.&40.VT,)(7.&40.+1.)R9.R8.R7.R6.)O>.(7.&40.+48174.)O=.(2:.(13.&40.))R1.(2;.$2.)))(0.(1<.(4.(2<.$1:.$1:.)(2=.$1:.$1:.Vlo,(16.VSPA,-80.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.(16.VCHB,+8.)(16.VCHB,+10.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.VSUB,(16.VSUB,(4?.(43.Vn,)+8.)))(4.(2<.$1:.$1:.)(2=.$1:.$1:.VPGS,(16.VPGS,+1.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.(16.VT,+:?0.)(16.VT,+<60.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.VUB,(16.VUB,VKF,))(8.(2<.$1:.$1:.))))))))O1.R1.)(0.(2>.$2.O1.R1.)(0.(2?.$2.R1.)(0.(49.R1.VSPA,O3.+1.(7.&40.+47:64.)(7.&40.VSP,)(7.&40.Vn,)(7.&40.$28.)(7.&40.+1.)(7.&40.VSTK,)(7.&40.(16.VSP,-51.))O9.O8.O7.O6.O5.O4.)(0.(30.$2.R1.VCHB,(4.$5.(6.O;.)(4.$5.(6.(7.&8.O:.))(4.$5.(47.(7.&40.=))(4.$5.(:.(7.&40.(43.Vn,)))(4.$5.(<.(7.&40.(50.(45.VTID,(38.+2.+20.))O<.)))(8.$5.)))))))(0.(30.$2.R1.VSUB,(4.$5.(12.(4<.(4?.(43.Vn,)+8.))(51.(13.&8.)(7.&8.=)(4<.(4?.(43.Vn,)+8.))))(8.$5.)))(0.(30.$2.R1.VPGS,(4.$5.(6.(52.Vn,O2.))(8.$5.)))(0.(30.$2.R1.(16.VT,+:?0.)(4.$5.(<.R5.)(4.$5.(<.R4.)(4.$5.(<.R3.)(8.$5.)))))(0.(31.$2.R1.(16.VT,+;60.)R2.)(0.(23.$32.(33.(13.&40.)R2.)#20.)(0.(30.$2.R1.VUB,(4.$5.(12.(4<.VKF,)(51.(13.&8.)(7.&8.+;>.)(4<.VKF,)))(8.$5.)))(34.$2.R1.Vlo,(16.VSPA,-80.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "01K0@L11019910313.28 L17054810462.24 L17135840957.24 L17784337564.19 L17882144120.26 L17882144120.28 L18607870801.24 L1905712448.19  L20302704847.28 L20573562197.28 L24886869106.146L24888640626.2  L24892837879.145L25320086065.28 L26069473972.27 L26400511621.24 L26631980436.24 L26631980436.28 L26704754027.24 L26876610421.24 L27697017043.3  L27705282402.5  L27848808849.2  L29786611176.10 L30862299178.24 L31736811297.28 L32045839665.28 L32382492013.2  L32541708167.27 L33128195209.19 L3318871087.24  L33292228550.19 L34800552535.28 L35243480162.26 L35243480162.27 L35243480162.28 L36193165570.2  L3661429958.2   L36786030869.28 L37881827237.26 L37881827237.27 L38235734261.1  L41008920023.19 L41864096740.8  L42198818825.19 L42363492789.26 L43089499825.19 L43214763655.27 L4323479075.28  L44029099751.0  L44345069824.10 L44355359517.19 L4819824607.27  L48535100989.24 L49301304837.26 L49301304837.27 L50627793533.24 L5172934059.24  L52016865498.28 L52481722021.27 L52657554222.19 L52877567872.10 L54497593123.28 L54570223649.3  L5629348309.24  L5629348309.26  L5629348309.27  L56319789689.24 L56393501986.19 L5808104861.19  L58913627406.0  L59619421015.27 L60525725327.28 L60925616309.26 L61030844230.120L61030858054.119L61545255186.24 L61545255186.27 L62099666698.24 L62727817027.28 L63221451435.27 L63370229784.121L63374621462.120L6425622916.19  L67266171279.28 L68053897848.26 L68053897848.28 L68489403102.24 L6913313913.19  L8936406121.26  L8936406121.27  00000\01:01Z02702e03S04604T05D05i06R06V07?07k08Y09L0:30:Z0;F0;o0<:0<B0<I0<W0=30=\0>H0>P0>i0?F0?_0@N0AT0B;0Bb0CI0CL0CP0D:0Dj0EX0E\0F>0FX0G50GZ0H70Hb0IG0IH0Ih0JM0K20KR0L70L\0M90M`0NH0O00OQ0P10PV0Pa0Q90QQ0Qi0R_0SA0S^0S_0TI0U10UV0VQ0WL0X20X]0Y90YV0ZL0[G0\B0\c0]K0^90^g0_E0_f0`I0`lS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS2H32H43SHR2H5S3hAR2SP1n2SB2pw3SPA1c2AB1H2H1S3hAR2SP1n2lo2SB2pw3SPA1c2AB3H12S3hAR2SP1n2SB2pw3SPA1c2AB3AB0S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2lo2SB2pw1c2AB3SPL2H43H12S3hAR2SP1n2SB2pw3SPA1c2AB4RZSBS3hAR2SP1n3CTX2SB2pw3SPA1c2AB5CTXNS3SHR2H32H42H5S3hAR2SP1n1T2SB2pw3SPA1c2AB2T01A1k2HkS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB3SB02bs2HLS2SPS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB3SB02bs2HLS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS3SHR2H32H42H5S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H02H22H83H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR3GEO2H12H32H42H52H7S3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR2H43H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB2H43H123SHRS3hAR2SP1n2lo2SB2pw3SPA1c2AB3GEO2H12H32H42H7S3hAR2SP1n2lo2SB2pw1c2AB3SPL2H02H22H83H12S1n3N2E3NDBS1n1H2H0S2SP2loS1n2SB2pw1c2ABS3hAR2SP1n2SB2pw3SPA1c2AB2H3S3hAR2SP1n3CTX2SB2pw3SPA1c2AB5CTXNS2H32H4S3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS3SHR2H32H42H5S2SP3SPHS3hAR2SP1n2SB2pw3SPA1c2ABS3hAR2SP1n2SB2pw3SPA1c2AB3NFBS3hAR2SP1n2SB2pw3SPA1c2ABS3hAR2SP1n2SB2pw3SPA1c2AB4RZSB3NFB3N2B3MNF4RNG'S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB3ABT3TNS3GEO2H12H02H32H42H62H82H73SHR2H5S3hAR2SP1n2lo2SB2pw3SPA1c2AB1A1k2Hk3H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB1A1k2Hk3H12S3hAR2SP1n2lo2SB2pw3SPA1c2AB1A1k2Hk3H12S1nS2SPS3hAR2SP1n3CTX2SB2pw3SPA1c2AB3ABC2H12H02H8S3hAR2SP1n2lo1T2SB2pw1c2AB2T12H12H02H22H82H93H12S3hAR2SP1n2lo1T2SB2pw1c2AB3SPL2T12H12H02H23H12S2loS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMGS3hAR1n2SB2pw1c2AB3AB13RNGS3hAR2SP1n2SB2pw3SPA1c2AB3NFBS3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H0S3hAR2SP1n2SB2pw3SPA1c2AB3N2BS3hAR2SP1n2lo1T2SB2pw1c2AB3SPL2T12H02H23H12S3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS2H32H4SS3hAR2SP1n2lo2SB2pw3SPA1c2AB3GEOS3hAR2SP1n2SB2pw3SPA1c2AB3NFB3DNF3MNFS3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H0S3hAR2SP1n2lo2SB2pw3SPA1c2AB3H12S3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk1H2H1S3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk1H2H1S3hAR2SP1n2SB2pw3SPA1c2AB3SHRS3hAR2SP1n2lo2SB2pw1c2AB3SPL3SHR2H43H12S3hAR2SP1n2lo3CTX2SB2pw3SPA1c2AB3CX13H12S3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H02H8S3hAR2SP1n2SB2pw3SPA1c2AB3DNF3MNFS3hAR2SP1n2lo2SB2pw3SPA1c2AB3GEOS3hAR2SP1n1T2SB2pw3SPA1c2AB3TNS2H32H4S2SP2lo3SPLS3hAR2SP1n2lo2SB2pw1c2ABS3hAR2SP1n2lo2SB2pw1c2ABS3hAR2SP1n2lo2SB2pw1c2ABS3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR3GEO2H12H32H42H52H82H7S3hAR2SP1n2SB2pw3SPA1c2AB3AB04RZSBS3hAR2SP1n2SB2pw3SPA1c2AB3AB1SS3hAR2SP1n2SB2pw3SPA1c2AB3SHR1A1k2Hk2H32H5S3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H02H8S3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H0S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n2lo2SB2pw3SPA1c2AB2H02H23H12S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H02H23H12S3hAR2SP1n2SB2pw3SPA1c2AB2H3S3hAR2SP1n2SB2pw3SPA1c2AB3SHRS3hAR2SP1n2lo2SB2pw3SPA1c2AB3SHR3GEO2H12H32H42H52H82H7S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2bs2HLS3hAR2SP1n2SB2pw3SPA1c2AB3AB13N2BS3hAR2SP1n1T2SB2pw3SPA1c2AB3ABT2H12H02H8S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2lo1T2SB2pw3SPA1c2AB2T12H12H02H23H12S3hAR2SP1n2SB2pw3SPA1c2AB1H2H1S3hAR2SP1n2lo2SB2pw3SPA1c2AB4SPALS3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk2H3S3hAR2SP1n2SB2pw3SPA1c2AB1A1k2Hk2H3". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK NB FP LOIMG SPL SPH SPA16 T0 T1 CX0 CX1 TC TIDB SB0 SBAL AB0 AB1 ABT ABC ASB TNS CTXNS"] Lemma msegC1 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Pgp,(13.&40.)Px5,(13.&40.)Px6,(13.&40.)Px7,(13.&40.)Px11,(13.&40.)Px12,(13.&40.)Px13,(13.&40.)Px14,(13.&40.)Px15,(13.&40.)Px16,(13.&40.)Px17,(13.&40.)Px28,(13.&40.)Pt4,(13.&40.)Pt5,(13.&40.)Pt6,(13.&40.)Pq6,(13.&40.)Pq7,(13.&40.)Pq8,(13.&40.)Pq9,(13.&40.)Pq10,(13.&40.)Pq11,(13.&40.)Pb0,(13.&8.)Pshb,(13.&8.)Ppgb,(13.&8.)Pw8,(13.&40.)Pj0,(13.&40.)Pj1,(13.&40.)Pj2,(13.&40.)PF,(36.&5.(13.&40.))Pfc,(13.&20.)Pm,P,(13.&40.)(19.(13.&8.))Pid,$1:.Pb1,$1:.Psj,(17.(13.&8.))Puj,(17.(13.&8.))Pfr0,(17.(13.&8.))Pbs,(17.(13.&40.))P,(0.(1=.=R6.)(37.R6.(38.+2.+1?.)))P,(0.(1=.=R6.)(37.R6.+100.))P,(53.(23.$1:.(3:.&8.R11.)=))P,(3<.(1=.(16.VAB,(44.Vn,))+7???8000.)(1=.+10007???8000.VAB,))P,(1?.R;.VT,VCTX,)P,(3>.VCS,VT,+1000.)P,(3>.VCS,VCTX,+10000.)P,(54.R>.)P,(20.R?.)P,(1.$2.R10.$55.(4.$5.(<.(7.&40.$56.))(8.$5.)))P,(1.$2.R11.$57.(4.$5.(6.(7.&8.+1.))(8.$5.)))P,(3>.VCS,VAB,(44.Vn,))P,(30.$2.R13.VCHB,(4.$5.(6.R1<.)(4.$5.(6.(7.&8.R11.))(4.$5.(47.(7.&40.=))(4.$5.(:.(7.&40.(43.Vn,)))(4.$5.(<.R19.)(8.$5.)))))))P,(1.$2.R14.(16.+7???8000.(58.VAB,+3.))(4.$5.(6.R1<.)(8.$5.)))P,(30.$2.R15.VSUB,(4.$5.(12.(4<.(4?.(43.Vn,)+8.))R12.)(8.$5.)))P,(30.$2.R16.VPGS,(4.$5.(6.R1=.)(8.$5.)))P,(30.$2.R17.(16.VT,+:?0.)(4.$5.(<.R1<.)(4.$5.(<.R1;.)(4.$5.(<.R1:.)(8.$5.)))))P,(31.$2.R18.(16.VT,+;60.)R12.)P,(23.$32.(33.(13.&40.)R13.)#20.)P,(30.$2.R1:.VUB,(4.$5.(12.(4<.VKF,)R16.)(8.$5.)))P,(49.R1;.VSPA,R16.+1.(7.&40.+47:64.)(7.&40.VSP,)(7.&40.Vn,)(7.&40.$28.)(7.&40.+1.)(7.&40.VSTK,)(7.&40.(16.VSP,-51.))R2:.R29.R28.R27.R26.R25.)P,(34.$2.R1<.Vlo,(16.VSPA,-80.))P,(3>.VCS,Vlo,(3;.VSP,Vlo,))P,(2?.$2.R1>.)(40.$2.VAL,VCS,(59.R3=.R21.R20.R1>.R28.R1=.R2>.R2=.R2<.R2;.R2:.R29.R1:.R26.R1?.)(24.(25.(7.&40.+47>40.)(7.&40.(16.VSPA,-80.))R3=.(7.&40.$26.)R3<.R3;.R3:.(7.&40.+1.)(7.&40.(43.Vn,))(7.&40.R1>.)R39.R38.R37.R36.R35.R34.R33.(7.&40.VAB,)(7.&40.(44.Vn,))(7.&40.VUB,)(7.&40.VCHB,)(7.&40.$27.)(7.&40.VSTK,)(7.&40.(45.VTID,(38.+2.+20.)))(7.&40.(16.VUB,(43.Vn,)))(7.&40.VT,)(7.&40.+1.)R32.R31.R30.R2?.)R21.(7.&40.+47>40.)R20.(2:.(13.&40.))R1?.(2;.$2.)))")
(* [comment removed for export] *).
    Proof.
      intros gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 t4 t5 t6 q6 q7 q8 q9 q10 q11 b0 shb pgb w8 j0 j1 j2 F fc m id b1 sj uj fr0 bs
        IDB B1B SHB RNG AS TCS CTXCS PS FS GOTFL PPART ACS HDR SHC SH PGC STH STB HL UC FR ST SCS MI.
      facts. pose proof needed2_primary as [N2E NDB]. pose proof AB_al as ABAL. pose proof (rz_size_bound n) as RZSB.
      assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
      assert (N2B : nfix n + rz_size n <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
        unfold nfix; clear - H H0 NB RZSB; lia. }
      pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MNF.
      assert (RNG' : (AB + needed2 n <= 0x7fff8000) \/ (0x10007fff8000 <= AB /\ AB + needed2 n <= ACEIL)) by (clear - RNG AB1; lia).
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2128 + -16) with (SP + (-134) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_mid AL IMG ALWF CS CSOK ASB) with (W := []) (t3 := x28);
          [ exact NB | exact FP | exact AB0 | exact ABAL | exact RNG' | exact TIDB | exact IDB | exact B1B | exact SHB | exact ACS | exact HDR | exact SHC | exact SH | exact PS
          | exact ST | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI ]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (x1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & MI1 & HDR1 & SH1 & ST1)).
      unfold segC1_post. subst PGS SUB KF CHB UB.
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
      { eapply (alloc_fill AL IMG ALWF CS CSOK) with (W := []) (uj := uj) (fill := 1);
          [ exact NB | exact AB0 | exact AB1 | clear; lia | exact ACS | | | | exact ST3 | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | exact MI3 ].
        - intros _. eapply rw_cells_transport; [| exact MU3| exact WM3|].
          { eapply rw_cells_transport; [exact UC| exact MU02| exact WM02|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; lia). clear - GEO SHR. decompose [and] GEO. repeat split; lia. }
          cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; lia). clear - GEO T1 TNS ABT. decompose [and] GEO. repeat split; lia.
        - eapply (fin_statics_transport _ m2 m3); [| exact MU3| intros A k Hk; cbn [disjoint_from]; clear - GEO Hk T0; decompose [and] GEO; repeat split; lia].
          eapply (fin_statics_transport _ m m2 FS MU02). intros A k Hk; cbn [disjoint_from]; clear - GEO Hk SHR; decompose [and] GEO; repeat split; lia.
        - unfold allocA_frame in *. eapply rw_cells_transport; [| exact MU3| exact WM3|].
          { eapply rw_cells_transport; [exact FR| exact MU02| exact WM02|]. cbn [disjoint_from cells_size csize Nat.add]. clear - GEO SHR SPL. subst SPA. decompose [and] GEO. repeat split; lia. }
          cbn [disjoint_from cells_size csize Nat.add]. clear - GEO T1 ABT CR. subst SPA. decompose [and] GEO. repeat split; lia. }
      cbn beta. (intros ms4 dd_H; ddestruct dd_H as (v1 & v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & w28 & w29 & w30 & w31 & m4 & -> & MU4 & WM4 & MI4 & FILL & _ & ST4)).
      specialize (FILL ltac:(clear; lia)).
      (* [comment removed for export] *)
      apply evtA_done. deexists 17. dexists k0, k1, k2, bs'. exists m4. split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU02]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_trans. { eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
               eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]. clear. intros x Hx. tauto. }
      split; [eapply wmono_trans; [exact WM02| eapply wmono_trans; [exact WM3| exact WM4]]|]. split; [exact MI4|].
      assert (MU24 : munch [(lo, SPA + -128); (T + 2800, T + 3168); (AB + rz_size n, AB + rz_size n + Z.min (nfix n) 4096)] m2 m4).
      { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM24 : wmono asegs m2 m4) by (eapply wmono_trans; [exact WM3| exact WM4]).
      assert (MU14 : munch [(lo, SPA + -128); (2147450880 + Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3, 2147450880 + Z.shiftr (AB + rz_size n + nfix n / 8 * 8) 3 + 1);
                            (T + 2800, T + 3168); (AB + rz_size n, AB + rz_size n + Z.min (nfix n) 4096)] m1 m4).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
        eapply munch_weaken; [| exact MU24]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM14 : wmono asegs m1 m4) by (eapply wmono_trans; [exact WM2| exact WM24]).
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
      split; [exact HL3|]. split; [exact FILL| exact ST4].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition segC2_post (ra gp : word) (F : bvmap 5 word) (fc : bv 32) (id : Z) (b1 : Z)
        (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Lms',$21.(22.(13.&40.)Lt0,(13.&40.)(22.(13.&40.)Lt1,(13.&40.)(22.(13.&40.)Lt2,(13.&40.)(22.(13.&40.)La1,(13.&40.)(22.(13.&40.)La2,(13.&40.)(22.(13.&40.)La3,(13.&40.)(22.(13.&40.)La4,(13.&40.)(22.(13.&40.)La5,(13.&40.)(22.(13.&40.)La6,(13.&40.)(22.(13.&40.)La7,(13.&40.)(22.(13.&40.)Lt3,(13.&40.)(22.(13.&40.)Lt4,(13.&40.)(22.(13.&40.)Lt5,(13.&40.)(22.(13.&40.)Lt6,(13.&40.)(22.P,(13.&40.)(19.(13.&8.))Lm',P,(13.&40.)(19.(13.&8.))(0.(23.$21.R10.(24.(25.O13.(7.&40.VSP,)O12.(7.&40.$26.)R?.R>.R=.O=.O<.(7.&40.VUB,)R<.R;.R:.R9.R8.R7.R6.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.R5.R4.R3.R2.)O11.(5:.O13.)O10.(2:.(13.&40.))R1.(2;.$2.)))(0.(1<.(4.(2<.$1:.$1:.)(2=.$1:.$1:.Vlo,VSP,)(4.(2<.$1:.$1:.)(2=.$1:.$1:.VCHB,(16.VCHB,+2.))(4.(2<.$1:.$1:.)(2=.$1:.$1:.VAB,(16.VAB,+10.))(8.(2<.$1:.$1:.)))))O1.R1.)(0.(2>.$2.O1.R1.)(0.(2?.$2.R1.)(0.(30.$2.R1.VCHB,(4.$5.(6.(7.&8.$5;.))(4.$5.(6.(7.&8.(48.O>.+?3.)))(4.$5.(47.(7.&40.=))(4.$5.(:.(7.&40.(43.Vn,)))(4.$5.(<.(7.&40.(50.(45.VTID,(38.+2.+20.))O?.)))(8.$5.)))))))(0.P,(37.+10.(5<.Vn,))(30.$2.R2.VAB,(4.$5.(<.(7.&40.$5=.))(4.$5.(<.(7.&40.VCHB,))(8.$5.))))(34.$2.R1.Vlo,VSP,))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@L11380347005.3  L12589220599.18 L13897832744.3  L15036699472.150L15455868178.3  L18979546931.3  L19089317658.144L21108182031.18 L22042812341.3  L24888640626.2  L26934503891.3  L27418375329.0  L27705282402.5  L27848808849.2  L29105961052.3  L30887070864.15 L31747570154.0  L32382492013.2  L32446540627.3  L33945784403.3  L341863661.3    L36193165570.2  L3661429958.2   L38235734261.1  L38419474119.144L38871848245.3  L39367057843.3  L42333736447.14 L42629649926.2  L44714545569.0  L45706641970.1  L47703064245.3  L50463732076.3  L51170281442.18 L5423397493.2   L54570223649.3  L54702911965.154L59045368852.11 L59379581035.3  L61030858054.144L61653547298.152L6290825141.3   L63374621462.145L63988471514.156L649840551.2    L8870907987.3   L8873338536.3   00000;00g01201m02802?03203g03n04204=04>04F04M04X05<05=05E05P05[05f05i05m06106d06k07207R07Z07[07_07f08108k09309>0:90:`0:g0;b0<]0<d0=_0>Z0>^0>i0?4S2SP2lo3SPLS3hAR2SP1n2lo2SB2pw3SPA1c2AB4RZSB3NFB1A1k2H1S2SP2lo3SPLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SP2lo3SPLS2SP2loS3hAR2SP1n1T2SB2pw1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB13NFB3N2B1A1k2H2S2SP2loS2SPS2SP2lo3SPLSS1n1H2H0S2SP2loS2SP2lo3SPLS2SP1n2lo2SB2pw3SPA1c2AB3CHB1x2Hx2H3SS2SP3SPHS2SP2lo3SPLS2SP2lo3SPLS2SP2lo3SPLS1nS2SPS2loS3hAR2SP1n1T2SB2pw1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SP2loS2SP2loS2SP1n2lo2SB2pw1c2AB3CHB1x2Hx2H3S2SP3SPHSS2SPS2SP2loS2SP2lo3SPLS3hAR2SP1n2lo2SB2pw3SPA1c2AB5LOIMG3AB14RZSB3NFB3N2B1A1k2H2S2SP3SPHS2SP2lo3SPLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR1n2SB2pw1c2AB3AB03AB13N2E3NDB4RZSBS2SP2loS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SP2loS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SB03SUB3PGS2KF2ws2HLS2SPS2SP2lo3SPLS2SP2lo3SPL". (* [comment removed for export] *)
    #[using="hAR IMG ALWF CSOK NB FP LOIMG SPL SPH SPA16 SB0 SBAL AB0 AB1 SUB PGS KF"] Lemma msegC2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocC ()) "Pra,(13.&40.)Pgp,(13.&40.)Px1,(13.&40.)Px5,(13.&40.)Px6,(13.&40.)Px7,(13.&40.)Px10,(13.&40.)Px11,(13.&40.)Px12,(13.&40.)Px13,(13.&40.)Px14,(13.&40.)Px15,(13.&40.)Px16,(13.&40.)Px17,(13.&40.)Px22,(13.&40.)Px28,(13.&40.)Pt4,(13.&40.)Pt5,(13.&40.)Pt6,(13.&40.)Pq0,(13.&40.)Pq1,(13.&40.)Pq2,(13.&40.)Pq3,(13.&40.)Pq4,(13.&40.)Pq5,(13.&40.)Pq6,(13.&40.)Pq7,(13.&40.)Pq8,(13.&40.)Pq9,(13.&40.)Pq10,(13.&40.)Pq11,(13.&40.)Pmg0,(13.&40.)Pmg1,(13.&40.)Pb0,(13.&8.)PF,(36.&5.(13.&40.))Pfc,(13.&20.)Pm,P,(13.&40.)(19.(13.&8.))Pid,$1:.Pb1,$1:.Psize,$1:.Pfr0,(17.(13.&8.))Pfr1,(17.(13.&8.))Pfr2,(17.(13.&8.))Pws,(17.(13.&40.))P,(0.(1=.=R6.)(37.R6.+100.))P,(3>.VCS,VAB,(44.Vn,))P,(20.R:.)P,(30.$2.R;.VCHB,(4.$5.(6.R>.)(4.$5.(6.(7.&8.R9.))(4.$5.(47.(7.&40.=))(4.$5.(:.(7.&40.(43.Vn,)))(4.$5.(<.(7.&40.(50.(45.VTID,(38.+2.+20.))R:.)))(8.$5.)))))))P,P,(37.+10.(5<.Vn,))(30.$2.R=.VAB,(4.$5.(<.R12.)(4.$5.(<.R11.)(8.$5.))))P,(49.R=.VSPA,R9.+1.(7.&40.+47:64.)(7.&40.VSP,)(7.&40.Vn,)(7.&40.$28.)(7.&40.+1.)(7.&40.VSTK,)(7.&40.(16.VSP,-51.))R18.R17.R16.R15.R14.R13.)P,(30.$2.R>.(16.VSTK,-10.)(4.$5.(<.(7.&40.VSP,))(4.$5.(<.(7.&40.+6978<.))(8.$5.))))P,(30.$2.R?.(16.VSP,-38.)(4.$5.(<.R1;.)(4.$5.(<.R1<.)(4.$5.(<.R1=.)(4.$5.(<.R1>.)(4.$5.(<.R1?.)(4.$5.(<.R20.)(4.$5.(<.R33.)(8.$5.)))))))))P,(30.$2.R10.VSTK,(4.$5.(<.(7.&40.(16.VSTK,+10.)))(4.$5.(<.(7.&40.R=.))(8.$5.))))P,(31.$2.R11.(16.VSTK,+10.)R:.)P,(23.$32.(33.(13.&40.)R;.)#1>.)P,(30.$2.R13.(16.VSTK,+100.)(4.$5.(12.#708.R>.)(8.$5.)))P,(30.$2.R14.(16.VSTK,+808.)(4.$5.(<.(7.&40.VSP,))(8.$5.)))P,(30.$2.R15.(16.VSTK,+810.)(4.$5.(12.#8.R?.)(8.$5.)))P,(34.$2.R16.Vlo,(16.VSPA,-80.))P,(3>.VCS,Vlo,(3;.VSP,Vlo,))P,(2?.$2.R18.)(40.$2.VAL,VCS,(5>.R3=.R3<.R1;.R1:.R18.R17.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R19.)(24.(25.R3;.(7.&40.(16.VSPA,-80.))R3<.(7.&40.$26.)R3:.R39.R38.(7.&40.+1.)(7.&40.(43.Vn,))R37.R36.R35.R34.R33.R32.R31.R30.(7.&40.VAB,)(7.&40.(44.Vn,))(7.&40.VUB,)(7.&40.VCHB,)R2?.(7.&40.VSTK,)(7.&40.(45.VTID,(38.+2.+20.)))(7.&40.(16.VUB,(43.Vn,)))(7.&40.VT,)(7.&40.+1.)R2>.R2=.R2<.R2;.)R1;.(7.&40.+48174.)R1:.(2:.(13.&40.))R19.(2;.$2.)))")
(* [comment removed for export] *).
    Proof.
      intros ra gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 t4 t5 t6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 mg0 mg1 b0 F fc m id b1 size fr0 fr1 fr2 ws
        B1B ACS FS HDR MG FR AFR FR7 STKC HTR HL F1800 TFB F8 ST SCS MI.
      facts. pose proof needed2_primary as [N2E NDB]. pose proof AB_al as ABAL. pose proof (rz_size_bound n) as RZSB.
      assert (SPAL : lo <= SPA - 512) by (subst SPA; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. replace (SP + -2128 + -16) with (SP + (-134) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
      assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA; clear; lia]).
      unfold segC2_post.
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (alloc_fin2 AL IMG ALWF CS CSOK) with (W := []) (mg0 := mg0) (mg1 := mg1);
          [ exact NB | exact AB0 | exact ABAL | exact AB1 | exact B1B | exact ACS | exact HDR | exact MG | exact FS | exact FR
          | exact ST | exact LOIMG | exact SPAL | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI | reflexivity ]. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & MI1 & HDR1 & MG1 & ST1)).
      replace (ret_pc (Z_to_bv 64 0x47a64)) with (Z_to_bv 64 0x47a64) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      fold UB in HDR1 |- *. fold CHB in MU1, HDR1, MG1 |- *.
      assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
      assert (N2B : nfix n + rz_size n <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
        unfold nfix; clear - H H0 NB RZSB; lia. }
      assert (DJ1 : forall A k, (A + k <= lo \/ SPA <= A) -> lo <= A -> disjoint_from [(lo, SPA); (CHB, CHB + 2); (AB, AB + 16)] A k).
      { intros A k H1 H2. cbn [disjoint_from]. subst CHB UB. clear - H1 H2 AB1 LOIMG RZSB NFB N2B. repeat split; lia. }
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (amalloc_ok AL IMG ALWF CS CSOK) with (SP := STK) (W := [(CHB, CHB + 2); (AB, AB + 16)]) (m0 := m);
          [ | | | exact LOIMG | subst STK; clear - SPL; lia | subst STK; clear - SPH; lia | | | | exact WM1 | exact MI1 ].
        - subst UB. clear - AB0 AB1 RZSB NDB N2E. lia.
        - replace (STK + -16) with SPA by (subst STK SPA; lia). eapply rw_cells_transport; [exact AFR| exact MU1| exact WM1| apply DJ1; cbn; subst SPA STK; clear - SPL; lia].
        - replace (STK + -16) with SPA by (subst STK SPA; lia). exact ST1.
        - subst STK. clear - SPA16. replace (SP + -2128) with (SP + (-133) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16.
        - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst STK; clear; lia].
        - replace STK with (SPA + 16) by (subst STK SPA; lia). eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
      cbn beta. intros ms2 (-> & ST2).
      replace (ret_pc (Z_to_bv 64 0x6978c)) with (Z_to_bv 64 0x6978c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      (* [comment removed for export] *)
      assert (ST3 : stk asegs m1 lo (SP + -56)).
      { assert (STKC1 : rw_cells asegs m1 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)])
          by (eapply rw_cells_transport; [exact STKC| exact MU1| exact WM1| apply DJ1; cbn; subst STK SPA; clear - SPL; lia]).
        pose proof (stk_release asegs m1 lo STK _ ST2 STKC1 ltac:(subst STK; clear - SPL; lia)) as R0. cbn [cells_size csize Nat.add] in R0.
        assert (HTR1 : u64arr asegs m1 (STK + 16) ws)
          by (eapply u64arr_transport; [exact HTR| exact MU1| exact WM1| apply DJ1; rewrite ?HL; cbn; subst STK SPA; clear - SPL; lia]).
        assert (TRC : rw_cells asegs m1 (STK + Z.of_nat 16) [CB (length (u64s ws)) (u64s ws)]).
        { replace (STK + Z.of_nat 16) with (STK + 16) by lia. apply rw_cells_of_u8arr. destruct HTR1 as [HB HW]. split; [exact HB|]. rewrite u64s_length, HL. rewrite HL in HW. replace (Z.of_nat (8 * 30)) with (8 * Z.of_nat 30) by (clear; lia). exact HW. }
        pose proof (stk_release asegs m1 lo _ _ R0 TRC ltac:(subst STK; clear - SPL; lia)) as R1. cbn [cells_size csize Nat.add] in R1. rewrite u64s_length, HL in R1.
        assert (F1800' : rw_cells asegs m1 (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) [CB 1800 fr1]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) with (STK + 256) by lia.
          eapply rw_cells_transport; [exact F1800| exact MU1| exact WM1| apply DJ1; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m1 lo _ _ R1 F1800' ltac:(subst STK; clear - SPL; lia)) as R2. cbn [cells_size csize Nat.add] in R2.
        assert (TFB' : rw_cells asegs m1 (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) [C8 (Z_to_bv 64 SP)]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) with (STK + 2056) by lia.
          eapply rw_cells_transport; [exact TFB| exact MU1| exact WM1| apply DJ1; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m1 lo _ _ R2 TFB' ltac:(subst STK; clear - SPL; lia)) as R3. cbn [cells_size csize Nat.add] in R3.
        assert (F8' : rw_cells asegs m1 (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) [CB 8 fr2]).
        { replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) with (STK + 2064) by lia.
          eapply rw_cells_transport; [exact F8| exact MU1| exact WM1| apply DJ1; cbn; subst STK SPA; clear - SPL; lia]. }
        pose proof (stk_release asegs m1 lo _ _ R3 F8' ltac:(subst STK; clear - SPL; lia)) as R4. cbn [cells_size csize Nat.add] in R4.
        lazymatch type of R4 with stk _ _ _ ?hi => replace hi with (SP + -56) in R4 by (subst STK; clear; lia) end. exact R4. }
      assert (FR7' : rw_cells asegs m1 (SP + -56) [C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra])
        by (eapply rw_cells_transport; [exact FR7| exact MU1| exact WM1| apply DJ1; cbn; subst SPA; clear - SPL; lia]).
      (* [comment removed for export] *)
      eapply evtA_mono.
      { subst STK. eapply (malloc_epi AL IMG ALWF CS CSOK); [exact FR7'| exact ST3| exact LOIMG| clear - SPL; lia| clear - SPH; lia| exact SPA16| exact SCS| exact MI1]. }
      cbn beta. intros ms3 (-> & ST4).
      deexists 14. exists m1. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. subst SPA. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
      split; [exact WM1|]. split; [exact MI1|]. split; [exact HDR1|]. split; [exact MG1| exact ST4].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End SegB.
End MallocC.

End ARUN_1.
