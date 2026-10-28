(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_AllocA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_MallocB () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.A_ALLOCATE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.A_ASAN_MALLOC"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_ERRNO"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"].

Section ARUN_1. Context {hAR : arun}.
Definition A_ASAN_MALLOC : Z := 0x47a38.
Definition A_ERRNO : Z := 0x63c9ec.        (* [comment removed for export] *)

Section MallocB.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L13049257242.59L16901428961.57L19516900705.56L23585410382.58L25936553270.56L31947592630.57L39302203090.55L4838750501.59 L49698585326.59L49698585326.60L55262987142.57L60388966608.58L60388966608.59L63468839727.59L6597240291.58 L7243903434.58 00000;00F00Q00Y00h01701F01N01c02802@02R02d02l03703?S3hAR2SP2HBS3hAR2SP2loS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP3SPH2HB5Ha_stS3hAR2SP3SPH2HB5Ha_stS3hAR2SPS3hAR2SP2lo3SPL2HBS3hAR2SP2lo3SPL2HBS3hAR2SPS3hAR2SP2HBS3hAR2SP". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma amalloc_pro : ltac2:(CDefT.buildp (gd_tbl_AW_MallocB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$1.Pn,$1.PSTK,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))P,(4.(5.=R6.)(6.R6.(7.+2.+40.)))P,(4.(5.=R6.)(6.R6.(7.+2.+40.)))P,(8.$9.R3.R6.R9.)P,(5.(:.VhAR,)R7.)P,(5.R8.(;.R;.+10.))P,(5.R<.(7.+2.+3>.))P,(<.$1.(=.R=.+10.)=)P,(>.VCS,R;.(;.R>.R;.))P,(?.$9.R9.)(10.$9.VAL,VCS,Lms',$11.(12.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(4.(<.$11.R2.(13.(14.(15.&40.+47:64.)(15.&40.(16.R12.-10.))R2=.R2<.R2;.R2:.R29.R28.R27.(15.&40.$17.)(15.&40.R11.)(15.&40.+8.)(15.&40.R10.)(15.&40.+1.)(15.&40.+1.)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R>.(15.&40.$18.)R=.(19.(0.&40.))R1.(1:.$9.)))(4.(1;.(1<.(1=.$1.$1.)(1>.$1.$1.R?.R12.)(1?.(1=.$1.$1.)))R<.R1.)(4.(20.$9.R<.R1.)(4.(?.$9.R1.)(4.(21.$9.R1.(16.R12.-10.)(1<.$22.(23.R28.)(1<.$22.(23.R2>.)(1?.$22.))))(8.$9.R1.R?.(16.R12.-10.))))))))(13.(14.R2<.(15.&40.R10.)R2;.R2:.R29.R28.R27.R26.R25.(15.&40.R?.)(15.&40.R>.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R<.(15.&40.$24.)R;.(19.(0.&40.))R:.(1:.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP n STK lo F fc m
      NB STKB ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_ASAN_MALLOC, A_ALLOCATE, A_INSTANCE in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L16901215969.58L19517080929.58L21991601993.58L23585410382.60L25936733494.58L29010569984.59L31947674550.58L31947674550.59L4838750501.60 L53578353676.59L59308632561.3 00000;00F00N00V00e01201A01P01X01`01iS3hAR2SP2loS3hAR2SP2loS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP1r2RBS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS1r2RB2KR". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma amalloc_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MallocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pqra,(0.&40.)PSP,$1.Pr,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))PW,(25.(1=.$1.$1.))P,(4.(6.=R7.)(6.R7.(7.+2.+40.)))P,(21.$9.R3.(16.R9.-10.)(1<.$22.(23.R;.)(1<.$22.(23.R:.)(1?.$22.))))P,(8.$9.R4.R8.(16.R:.-10.))P,(5.(:.VhAR,)R9.)P,(5.R:.(;.R<.+10.))P,(5.R=.(7.+2.+3>.))P,(<.$1.(=.R>.+10.)=)P,(>.VCS,R=.(;.R?.R=.))P,(1;.(1<.(1=.$1.$1.)(1>.$1.$1.R>.R10.)R9.)R;.R:.)P,(20.$9.R<.R;.)P,(?.$9.R<.)(10.$9.VAL,VCS,Lms',$11.(4.(<.$11.R1.(13.(14.R15.(15.&40.R14.)R32.R31.R30.R2?.R2>.R16.R2<.(15.&40.R13.)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R11.(26.R15.)R10.(19.(0.&40.))R>.(1:.$9.)))(8.$9.R>.R12.R14.))(13.(14.(15.&40.+47:64.)(15.&40.(16.R13.-10.))R31.R30.R2?.R2>.R2=.R2<.R2;.(15.&40.R12.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R10.(15.&40.+47:64.)R?.(19.(0.&40.))R=.(1:.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 qra SP r lo F fc m0 m W
      RB FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR. { exfalso. clear - KR RB. lia. }
    zstep. zstep. zstep. replace (SP + -16 + 16) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. split; [reflexivity| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L10404312199.62L16901084647.57L18503462193.60L1940395428.58 L19516687975.57L21991601993.57L23551740665.60L23585410382.59L25936864816.57L28041632991.62L31715192136.61L31947804848.57L31947804848.58L33022495329.58L33024608835.58L36040919858.60L37062217443.60L37481963854.60L37973069332.58L37975215670.58L4838750501.59 L49484649706.58L49698585326.61L49782145994.60L52155331762.60L53519968643.58L53578223370.58L53813608905.57L55178519161.58L61206667189.59L61580800532.62L64551436470.59L6653352558.58 L66904990446.58L6848192903.62 00000T00_00j01701B01J01^01f02502L02]02l03;03F03Q03Y03d03l04;04J04R04Z04o05705?05M05U05d05e05m06Q06`06m07207VS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2loS3hAR2SP2HBS3hAR2AL4IMG'S3hAR2SP2loS3hAR2SPS3hAR2SP2lo1W3SPL2HBS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2HB5Ha_st5Hl_stS3hAR2SP2HB5Ha_stS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2loS3hAR2SPS3hAR2SP2HBS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SP3SPH2HB5Ha_stS3hAR2SPS3hAR2SPS3hAR2AL5ALWF'S3hAR2SPS3hAR2SP2lo3SPLFS3hAR2SPS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hARS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma amalloc_null : ltac2:(CDefT.buildp (gd_tbl_AW_MallocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pqra,(0.&40.)Pe0,(0.&40.)PSP,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))PW,(25.(1=.$1.$1.))P,(21.$9.R2.(16.R7.-10.)(1<.$22.(23.R:.)(1<.$22.(23.R9.)(1?.$22.))))P,(21.$9.R3.$27.(1<.$22.(28.R9.)(1?.$22.)))P,(8.$9.R4.R8.(16.R9.-10.))P,(5.(:.VhAR,)R9.)P,(5.R:.(;.R;.+20.))P,(5.R<.(7.+2.+3>.))P,(<.$1.(=.R=.+10.)=)P,(>.VCS,R=.(;.R>.R=.))P,(1;.(1<.(1=.$1.$1.)(1>.$1.$1.R>.R?.)(1<.(1=.$1.$1.)(1>.$1.$1.$27.(16.$27.+4.))R9.))R;.R:.)P,(20.$9.R<.R;.)P,(?.$9.R<.)P,(<.(0.&40.)R30.(15.&40.$29.))(10.$9.VAL,VCS,Lms',$11.(12.(0.&40.)Lx11,(0.&40.)(12.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(4.(<.$11.R3.(13.(14.R18.(15.&40.R16.)R35.R34.R33.R32.R31.R19.R2?.(15.&40.=)R2.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R14.(26.R18.)R13.(19.(0.&40.))R1.(1:.$9.)))(4.(1;.(1<.(1=.$1.$1.)(1>.$1.$1.R15.R16.)(1<.(1=.$1.$1.)(1>.$1.$1.$27.(16.$27.+4.))R10.))R12.R1.)(4.(20.$9.R12.R1.)(4.(?.$9.R1.)(4.(21.$9.R1.$27.(1<.$22.(28.(15.&40.+<.))(1?.$22.)))(8.$9.R1.R15.R16.))))))))(13.(14.(15.&40.+47:64.)(15.&40.(16.R13.-10.))R32.R31.R30.R2?.R2>.R2=.R2<.(15.&40.=)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R11.(15.&40.+47:64.)R10.(19.(0.&40.))R>.(1:.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 qra e0 SP lo F fc m0 m W
      FR ER ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_ERRNO, A_TP in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR0 ST (SP + -16).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. replace (SP + -16 + 16) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. deexists 2. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [assumption| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10056250446.60L13012402650.58L13180431950.60L13900354957.58L13900354957.59L16905444186.58L1847227021.58 L18714218702.60L19521308890.58L25245533530.58L25924184205.58L2865985737.58 L31960227341.58L32551331534.60L33026492378.58L35714078135.59L37979210637.58L56609791438.60L61009545946.58L62489180965.60L64547441933.58L6652333612.59 L67188883034.58L68577470286.60L7882989581.58 00000800C00K00Z00i01401C01K01V01a02002802G02O02Z02b03103903D03L03[03c03n04604ES3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma malloc_epi : ltac2:(CDefT.buildp (gd_tbl_AW_MallocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)Pqra,(0.&40.)PSP,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))P,(21.$9.R1.(16.R5.-38.)(1<.$22.(23.R7.)(1<.$22.(23.R8.)(1<.$22.(23.R9.)(1<.$22.(23.R:.)(1<.$22.(23.R;.)(1<.$22.(23.R<.)(1<.$22.(23.R6.)(1?.$22.)))))))))P,(8.$9.R2.R5.(16.R6.-38.))P,(5.(:.VhAR,)R6.)P,(5.R7.(;.R8.+850.))P,(5.R9.(7.+2.+3>.))P,(<.$1.(=.R:.+10.)=)P,(>.VCS,R:.(;.R;.R:.))P,(?.$9.R8.)(10.$9.VAL,VCS,Lms',$11.(4.(<.$11.R1.(13.(14.R?.(15.&40.R>.)R33.R32.R31.R30.R2?.R15.R14.R2<.R2;.R2:.R29.R28.R27.R26.R25.R13.R12.R11.R10.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R<.(26.R?.)R;.(19.(0.&40.))R:.(1:.$9.)))(8.$9.R:.R=.R>.))(13.(14.R15.(15.&40.(16.R=.-850.))R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R;.(15.&40.+6978<.)R:.(19.(0.&40.))R9.(1:.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 q0 q1 q2 q3 q4 q5 qra SP lo F fc m
      FR ST LOIMG SPL SPH SPA SCS MI.
    facts.
    zstep. replace (SP + -2128 + 96) with (SP + -2032) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. replace (SP + -2032 + 2032) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. split; [reflexivity| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MallocB.

End ARUN_1.
