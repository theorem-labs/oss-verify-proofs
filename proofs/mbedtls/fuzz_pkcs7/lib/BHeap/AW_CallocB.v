(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_stringA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AW_Unwind AW_Unwind2 AW_MmapFixed AW_MallocA AW_Poison AW_AllocA AW_AllocB AW_MallocB.
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
Ltac2 gd_tbl_AW_CallocB () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.A_ALLOCATE"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.A_ASAN_CALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocB.A_ERRNO"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"].

Section ARUN_1. Context {hAR : arun}.
Definition A_ASAN_CALLOC : Z := 0x4841c.     (* [comment removed for export] *)

Section CallocB.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0?L15129414474.63L16901428961.61L1859764022.61 L19516900705.60L21142837706.63L24413464578.61L25936553270.60L26905125859.62L26905125859.63L27170469450.63L27335347790.63L29149214414.63L29874810585.65L31947592630.61L3276969806.62 L33022511713.61L33180861642.63L35497695249.65L37975166518.61L39302203090.59L39340114894.63L40202209158.61L40228640085.0 L42311576761.4 L45217263562.62L49698585326.63L49698585326.64L58142605646.63L60388966608.62L60388966608.63L61013493601.61L64551387318.61L67176444897.6100000800C00R00]00e00m01<01G01R01Z01b01j02V02e02m03803@03H03W03f03n04604704D04L04a05605>05P05b05m06<06GS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2HBS3hAR2SP2HBS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SP3cnt2sz1n2lo3CB03SZ02EN2NB5LOIMG3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPSS3cnt2sz1n2ENS3hAR2SPS3hAR2SP3SPH2HB5Ha_stS3hAR2SP3SPH2HB5Ha_stS3hAR2SPS3hAR2SP2lo3SPL2HBS3hAR2SP2lo3SPL2HBS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2lo". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma acalloc_pro : ltac2:(CDefT.buildp (gd_tbl_AW_CallocB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PSP,$1.Pcnt,$1.Psz,$1.Pn,$1.PSTK,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))P,(4.(5.=R8.)(6.R8.(7.+2.+40.)))P,(4.(5.=R8.)(6.R8.(7.+2.+40.)))P,(8.$1.R8.(9.R:.R9.))P,(6.R9.(7.+2.+40.))P,(4.(5.=R9.)(6.R9.(7.+2.+40.)))P,(:.$;.R6.R9.R>.)P,(5.(<.VhAR,)R:.)P,(5.R;.(=.R10.+30.))P,(5.R11.(7.+2.+3>.))P,(8.$1.(>.R12.+10.)=)P,(?.VCS,R>.(=.R13.R>.))P,(10.$;.R<.)(11.$;.VAL,VCS,Lms',$12.(13.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(13.(14.(0.&8.))Lfr,(14.(0.&8.))(4.(8.$12.R3.(15.(16.(17.&40.+48470.)(17.&40.(18.R18.-30.))R32.R31.R30.R2?.R2>.(17.&40.R15.)(17.&40.R14.)(17.&40.$19.)(17.&40.R15.)(17.&40.+8.)(17.&40.R14.)(17.&40.+1.)(17.&40.=)R28.R27.(17.&40.$19.)(17.&40.+1.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R12.(17.&40.$1:.)R11.(1;.(0.&40.))R2.(1<.$;.)))(4.(1=.(1>.(1?.$1.$1.)(20.$1.$1.R13.R18.)(21.(1?.$1.$1.)))R10.R2.)(4.(22.$;.R10.R2.)(4.(10.$;.R2.)(4.(23.$;.R2.(18.R18.-30.)(1>.$24.(25.#8.R1.)(1>.$24.(26.R25.)(1>.$24.(26.R26.)(1>.$24.(26.R2<.)(1>.$24.(26.R2=.)(1>.$24.(26.R33.)(21.$24.))))))))(:.$;.R2.R13.(18.R18.-30.)))))))))(15.(16.R30.(17.&40.R15.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(17.&40.R14.)(17.&40.R13.)(17.&40.R11.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R?.(17.&40.$27.)R>.(1;.(0.&40.))R=.(1<.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP cnt sz n STK lo F fc m
      CB0 SZ0 EN NB STKB ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_ASAN_CALLOC, A_ALLOCATE, A_INSTANCE in *.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 48%nat ST.
    apply (rw_cells_split_CB asegs _ (SP + -48) [] 48%nat _ [] [8; 8; 8; 8; 8; 8]%nat) in FR; [| cbn [sum_nat]; lia].
    cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (TAIL : forall a2x : word,
      evtA asegs AL CS
        (fun ms' => exists (m' : mem) (fr : list byte),
           ms' = MS (mkR (Z_to_bv 64 0x48470) (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 STK)
                        (Z_to_bv 64 0x106398) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 STK) (Z_to_bv 64 1) (Z_to_bv 64 0) a6 a7
                        (Z_to_bv 64 0x106398) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x47a94) fc None m' (seg_rom asegs)
           /\ munch [(lo, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ rw_cells asegs m' (SP + -48) [CB 8 fr; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\ stk asegs m' lo (SP + -48))
        (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 s0 (Z_to_bv 64 STK) (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2x a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x48444) fc None mf (seg_rom asegs)))
    end.
    { intros a2x.
      (* [comment removed for export] *)
      zstep. replace (sz * cnt) with n by (clear - EN; lia).
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evtA_done. cbn beta. deexists 2. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR| exact ST]. }
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - apply TAIL.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KM; zify_cond KM.
      + exfalso. apply KM. rewrite Z.shiftr_div_pow2 by (clear; lia). apply Z.div_small. clear - CB0 SZ0 EN NB. nia.
      + apply TAIL.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0?L13008276577.62L13010357315.62L13896095798.62L13898176532.62L13960923015.66L16901084647.61L18503462193.64L1859976240.61 L1940395428.62 L19516687975.61L23551740665.64L25936864816.61L27335347790.63L2777086687.66 L29149214414.63L31715192136.65L31947804848.61L3276969806.63 L33022724455.61L37974854960.61L39340114894.63L40482806454.63L42001773902.64L4216595690.62 L42303277385.61L45831443381.63L49440411594.64L49698585326.65L52155331762.64L53519968643.62L53842432647.66L5389242313.61 L55178519161.62L55985251122.64L57370105059.64L58142605646.63L61013836903.61L61580800532.66L63787281162.62L64551732144.61L6653352558.62 L66904990446.62L67176132839.61L7870246576.62 00000;00F00U00d01H01S01^01m02:02E02Y02h03003G03O03`03o04704B04Q04Y04h05005805@05H05P05e05m06;06_06n06o07707B07J07U08908A08P08]08b08m09<S3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2loS3hAR2SP2HBS3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hAR2SP2loS3hAR2SP2lo1W3SPL2HBS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2HB5Ha_st5Hl_stS3hAR2SPS3hAR2SP2HB5Ha_stS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SP3SPH2HB5Ha_stS3hAR2SPS3hAR2AL5ALWF'S3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2lo3SPLFS3hAR2SPS3hAR2SP2HBS3hAR2SPS3hAR2SP2loS3hAR2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SPS3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hARS3hAR2SP2loS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma acalloc_null : ltac2:(CDefT.buildp (gd_tbl_AW_CallocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pqra,(0.&40.)Pe0,(0.&40.)PSP,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr,(14.(0.&8.))PW,(14.(1?.$1.$1.))P,(23.$;.R3.(18.R8.-30.)(1>.$24.(25.#8.R2.)(1>.$24.(26.R;.)(1>.$24.(26.R<.)(1>.$24.(26.R=.)(1>.$24.(26.R>.)(1>.$24.(26.R:.)(21.$24.))))))))P,(23.$;.R4.$28.(1>.$24.(29.R:.)(21.$24.)))P,(:.$;.R5.R9.(18.R:.-30.))P,(5.(<.VhAR,)R:.)P,(5.R;.(=.R<.+40.))P,(5.R=.(7.+2.+3>.))P,(8.$1.(>.R>.+10.)=)P,(?.VCS,R>.(=.R?.R>.))P,(1=.(1>.(1?.$1.$1.)(20.$1.$1.R?.R10.)(1>.(1?.$1.$1.)(20.$1.$1.$28.(18.$28.+4.))R9.))R<.R;.)P,(22.$;.R=.R<.)P,(10.$;.R=.)P,(8.(0.&40.)R34.(17.&40.$2:.))(11.$;.VAL,VCS,Lms',$12.(13.(0.&40.)Lx11,(0.&40.)(13.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(4.(8.$12.R3.(15.(16.R19.(17.&40.R17.)R39.R38.R37.R36.R35.R1=.R1<.(17.&40.=)R2.R31.R30.R2?.R2>.R2=.R2<.R1;.R1:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R15.(2;.R19.)R14.(1;.(0.&40.))R1.(1<.$;.)))(4.(1=.(1>.(1?.$1.$1.)(20.$1.$1.R16.R17.)(1>.(1?.$1.$1.)(20.$1.$1.$28.(18.$28.+4.))R10.))R13.R1.)(4.(22.$;.R13.R1.)(4.(10.$;.R1.)(4.(23.$;.R1.$28.(1>.$24.(29.(17.&40.+<.))(21.$24.)))(:.$;.R1.R16.R17.))))))))(15.(16.(17.&40.+48470.)(17.&40.(18.R14.-30.))R36.R35.R34.R33.R32.R31.R30.(17.&40.=)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R12.(17.&40.+48470.)R11.(1;.(0.&40.))R?.(1<.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 qra e0 SP lo F fc m0 m fr W
      FR ER ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_ERRNO, A_TP in *.
    (* [comment removed for export] *)
    zstep. zstep.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR0 ST (SP + -48).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. replace (SP + -48 + 48) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. cbn beta. deexists 2. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [assumption| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L15615277569.68L16899434184.66L1861619487.66 L19518453064.66L19824759579.66L25935467807.66L27335347790.68L29010565920.69L29010566049.68L29010569984.67L29149214414.68L31945270175.66L3276969806.68 L33024129608.66L33693648140.66L37972131359.66L38793500428.66L39340114894.68L42303277385.67L48193359348.69L53522114977.66L58142605646.68L59308628433.5 L59308632561.3 L60735426886.66L61012424520.66L63790012453.68L64554512543.66L67178628040.66L7871700383.68 00000C00N00]00h00i01801@01M01Z01g01o02>02F02Q02V02e03203:03B03U03c03k04;04D04Q04\04d05305>05MS3hAR2SP2SB3SB03SBHS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loFS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP1r2RBS3hAR2SP1r2RBS3hAR2SP1r2RBS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hARS3hAR2SP2lo3SPLS3hAR2AL4IMG'S3hAR2SPS3hAR2SPS3hAR2SP2SB3SB03SBHS3hAR2AL5ALWF'S3hAR2SPS1r2SB3RSB2K12K2S1r2RB2KRS3hAR2AL4IMG'S3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma acalloc_ok_sec : ltac2:(CDefT.buildp (gd_tbl_AW_CallocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px1,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pqra,(0.&40.)PSP,$1.Pr,$1.Pn,$1.PSTK,$1.PSB,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr,(14.(0.&8.))PW,(14.(1?.$1.$1.))P,(4.(6.=R;.)(6.R;.(7.+2.+40.)))P,(5.=R9.)P,(6.(18.R:.(7.+2.+25.))(7.+2.+40.))P,(2<.(6.R>.R;.)(5.(18.R;.(7.+2.+25.))R>.))P,(2=.$;.R7.(18.$19.+20.)(1>.$24.(26.(17.&40.R<.))(21.$24.)))P,(23.$;.R8.(18.R11.-30.)(1>.$24.(25.#8.R7.)(1>.$24.(26.R13.)(1>.$24.(26.R14.)(1>.$24.(26.R15.)(1>.$24.(26.R16.)(1>.$24.(26.R12.)(21.$24.))))))))P,(:.$;.R9.R=.(18.R12.-30.))P,(5.(<.VhAR,)R>.)P,(5.R?.(=.R14.+30.))P,(5.R15.(7.+2.+3>.))P,(8.$1.(>.R16.+10.)=)P,(?.VCS,R12.(=.R17.R12.))P,(1=.(1>.(1?.$1.$1.)(20.$1.$1.R13.R18.)R=.)R10.R?.)P,(22.$;.R11.R10.)P,(10.$;.R11.)(11.$;.VAL,VCS,Lms',$12.(13.(0.&40.)Lx11,(0.&40.)(4.(8.$12.R2.(15.(16.R1>.(17.&40.R1=.)R3;.R3:.R38.R37.R36.R22.R21.(17.&40.R1<.)R1.R34.R33.R32.R31.R30.R2?.R20.R1?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R17.(2;.R1>.)R16.(1;.(0.&40.))R14.(1<.$;.)))(:.$;.R14.R18.R1=.)))(15.(16.R37.(17.&40.(18.R1;.-30.))R39.R38.R36.R35.R34.(17.&40.R19.)(17.&40.R18.)(17.&40.R1:.)R33.R32.R31.R30.R2?.R2>.R2=.(17.&40.$19.)(17.&40.+1.)R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R15.(17.&40.+48470.)R14.(1;.(0.&40.))R12.(1<.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 qra SP r n STK SB lo F fc m0 m fr W
      RB SB0 SBH RSB SBC FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_INSTANCE in *. change (0x106398 + 32) with 0x1063b8 in SBC.
    assert (EPI : forall (x11 x29 : word),
      evtA asegs AL CS
        (fun ms' => exists (x11 : word) , ms' = MS (mkR qra (Z_to_bv 64 SP) gp tp t0 t1 t2 q0 q1 (Z_to_bv 64 r) x11 a2 a3 a4 a5 a6 a7
                                 q2 q3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc qra) fc None m (seg_rom asegs)
                    /\ stk asegs m lo SP)
        (MS (mkR x1 (Z_to_bv 64 (SP + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 STK) (Z_to_bv 64 r) x11 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 0x106398) x29 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x484c4) fc None m (seg_rom asegs))).
    { intros x11 x29.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. replace (SP + -48 + 48) with SP by lia. zstep.
      release_frame FR ST SP.
      apply evtA_done. cbn beta. eexists. split; [reflexivity| exact ST]. }
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR. { exfalso. clear - KR RB. lia. }
    zstep. zstep. if_cases K1; zify_cond K1.
    - apply EPI.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + apply EPI.
      + exfalso. try (rewrite Z.mod_small in K2 by (clear - SB0 SBH; lia)). clear - K1 K2 RSB. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00`0@L15615277569.84 L16901084647.103L1859976240.103 L19516687975.103L19824759579.82 L25936864816.103L27335348173.105L28929411814.84 L29010565920.85 L29010566049.84 L29010569984.83 L29149214541.105L31947804848.103L3276969677.105 L33022724455.103L33693648140.82 L34088053676.84 L3487732589.5   L37281436902.84 L37974854960.103L3845658034.84  L38793500428.82 L39120847537.86 L39340114509.105L39924793106.82 L42303277385.103L48193359348.85 L53522110849.84 L53522114977.82 L56070819003.84 L57137267116.84 L58142605517.105L59308628304.4  L59308628433.4  L59308632561.3  L60735426886.82 L61013836903.103L63706774450.84 L63787281162.104L64551732144.103L64764229307.84 L65258828961.0  L66336766892.84 L67176132839.103L7001376283.6   L7870246576.104 L8265267294.0   L9545704876.84  00000C00N00]00h00i01801@01M01n02O03003803G03O03Z03_03l04;04H04W04X04e04m05505605>05Q05_05m05n06306;06H06U06^06k07607707?07N07O07P07U07`08308B08C08PS3hAR2SP2SB3SB03SBHS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loFS3hAR2SP2lo3SPLS3hAR2SPS3hAR2AL4IMG'S3hAR2SP1r1n2lo2R02N03RLO3SPL3SPHS3hAR2SP1r1n2lo2R02N03RLO3SPL3SPHS3hAR2SP1r1n2lo2R02N03RLO3SPL3SPHS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hARS3hAR2AL4IMG'S2SP1r1n2lo3RLOS3hAR2AL4IMG'S3hAR2SP2lo3SPLFS3hAR2AL4IMG'S3hAR2SPS3hAR2SPFS3hAR2SPS3hAR2SP2SB3SB03SBHS3hAR2AL5ALWF'S3hAR2AL5ALWF'FS3hARS3hAR2SPS1r2SB3RSB2K1S1r2SB3RSB2K2S1r2R02KRS3hAR2AL4IMG'S3hAR2SP2loFS3hAR2SPS3hAR2SP2lo3SPLFSS3hARS3hAR2SP2loS2SP1r1n2lo3RLO3SPLS3hAR2SP2lo3SPLSS3hAR2AL4IMG'". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma acalloc_ok_prim : ltac2:(CDefT.buildp (gd_tbl_AW_CallocB ()) "Pgp,(0.&40.)Ptp,(0.&40.)Px1,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pqra,(0.&40.)PSP,$1.Pr,$1.Pn,$1.PSTK,$1.PSB,$1.Plo,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pfr,(14.(0.&8.))Pjunk,(14.(0.&8.))PW,(14.(1?.$1.$1.))P,(6.=R<.)P,(5.=R<.)P,(6.(18.R>.R=.)(7.+2.+40.))P,(5.=R<.)P,(6.(18.R=.(7.+2.+25.))(7.+2.+40.))P,(4.(5.R>.R11.)(6.R11.(18.R>.(7.+2.+25.))))P,(2=.$;.R:.(18.$19.+20.)(1>.$24.(26.(17.&40.R?.))(21.$24.)))P,(2>.R;.)P,(23.$;.R<.R14.(1>.$24.(25.(2?.R13.)R:.)(21.$24.)))P,(?.VCS,R15.R14.)P,(5.(18.R16.R15.)R12.)P,(23.$;.R?.(18.R18.-30.)(1>.$24.(25.#8.R>.)(1>.$24.(26.R1:.)(1>.$24.(26.R1;.)(1>.$24.(26.R1<.)(1>.$24.(26.R1=.)(1>.$24.(26.R19.)(21.$24.))))))))P,(:.$;.R10.R14.(18.R19.-30.))P,(5.(<.VhAR,)R15.)P,(5.R16.(=.R1;.+30.))P,(5.R1<.(7.+2.+3>.))P,(8.$1.(>.R1=.+10.)=)P,(?.VCS,R19.(=.R1>.R19.))P,(1=.(1>.(1?.$1.$1.)(20.$1.$1.R1:.R1?.)(1>.(1?.$1.$1.)(20.$1.$1.R1>.(18.R1>.R1=.))R13.))R17.R16.)P,(22.$;.R18.R17.)P,(10.$;.R18.)(11.$;.VAL,VCS,Lms',$12.(13.(0.&40.)Ly0,(0.&40.)(13.(0.&40.)Ly1,(0.&40.)(13.(0.&40.)Ly2,(0.&40.)(13.(0.&40.)Lx11,(0.&40.)(13.(0.&40.)Lx12,(0.&40.)(13.(0.&40.)Lx13,(0.&40.)(13.(0.&40.)Lx14,(0.&40.)(13.(0.&40.)Lx15,(0.&40.)(13.(0.&40.)Lx16,(0.&40.)(13.(0.&40.)Lx17,(0.&40.)(13.(0.&40.)Ly3,(0.&40.)(13.(0.&40.)Ly4,(0.&40.)(13.(0.&40.)Ly5,(0.&40.)(13.(0.&40.)Ly6,(0.&40.)(13.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(4.(8.$12.R10.(15.(16.R33.(17.&40.R32.)R50.R4?.R?.R>.R=.R37.R36.(17.&40.R31.)R<.R;.R:.R9.R8.R7.R6.R35.R34.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R5.R4.R3.R2.)R2<.(2;.R33.)R2;.(1;.(0.&40.))R1.(1<.$;.)))(4.(1=.(1>.(1?.$1.$1.)(20.$1.$1.R2=.R32.)(1>.(1?.$1.$1.)(20.$1.$1.R31.(18.R31.R30.))R26.))R2:.R1.)(4.(22.$;.R2:.R1.)(4.(10.$;.R1.)(4.(23.$;.R1.R31.(1>.$24.(25.(2?.R30.)(30.(0.&8.)(17.&8.=)(2?.R30.)))(21.$24.)))(:.$;.R1.R2=.R32.)))))))))))))))))))))(15.(16.R3>.(17.&40.(18.R22.-30.))R40.R3?.R3=.R3<.R3;.(17.&40.R20.)(17.&40.R1?.)(17.&40.R21.)R3:.R39.R38.R37.R36.R35.R34.(17.&40.$19.)(17.&40.+1.)R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R1<.(17.&40.+48470.)R1;.(1;.(0.&40.))R19.(1<.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 qra SP r n STK SB lo F fc m0 m fr junk W
      R0 N0 RNH SB0 SBH RSB SBC FS UJ UCS RLO FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_INSTANCE in *. change (0x106398 + 32) with 0x1063b8 in SBC.
    dpose FS as (L1 & L2 & MGC & MH & GF & FMX & FFB & G5 & RM).
    unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET, A_MUSL_MEMSET in *.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR. { exfalso. clear - KR R0. lia. }
    zstep. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 RSB. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. try (rewrite Z.mod_small in K2 by (clear - SB0 SBH; lia)). clear - K2 RSB. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (A_memset_evtA_aok AL CS IMG) with (junk := junk); [exact UJ| exact MI| | | | | | reflexivity| reflexivity| reflexivity].
      - intros x Hx. left. apply UCS. exact Hx. - exact R0. - exact N0. - exact RNH. - clear; lia. }
    cbn beta. (intros ms2 dd_H; ddestruct dd_H as (z0 & z1 & z2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m' & -> & MUm & WMm & MIm & ZR)).
    replace (ret_pc (Z_to_bv 64 0x484a4)) with (Z_to_bv 64 0x484a4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    assert (FR' : rw_cells asegs m' (SP + -48) [CB 8 fr; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra])
      by (eapply rw_cells_transport; [exact FR| exact MUm| exact WMm| cbn [disjoint_from cells_size csize Nat.add]; clear - RLO SPL; lia]).
    assert (ST' : stk asegs m' lo (SP + -48)) by (eapply stk_transport_disjoint; [exact ST| exact MUm| exact WMm| cbn [disjoint_from]; clear - RLO; lia]).
    clear FR ST. rename FR' into FR. rename ST' into ST.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. replace (SP + -48 + 48) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. cbn beta. deexists 14. exists m'. split; [reflexivity|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MUm]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
    split; [exact (wmono_trans _ _ _ _ WM WMm)|]. split; [exact MIm|]. split; [exact ZR| exact ST].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CallocB.
End ARUN_1.
