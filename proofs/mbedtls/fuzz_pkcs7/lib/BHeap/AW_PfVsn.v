(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr Frame Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SeqExec EnframeArith.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib A_imsetv A_vsnp_num.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfNum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00280de3586da4fb 0 2 1 1 33 1P0082e5cfe8e7bc03 0 2 0 1 32 1P00d1e67e40f1beb4 0 2 0 1 52 1P00faafa71db9d282 0 2 0 1 30 1P00fe8351e50d7db6 0 2 0 1 52 1P022c3a574da58b35 0 2 1 1 33 1P03636d04bd68e119 0 2 0 1 32 1P03846dee771ce739 0 2 0 1 32 1P04ab30fc2c9cc092 0 2 1 1 49 1P05f8cc31044be40f 0 2 0 1 32 1P0676357d7829740d 0 2 0 1 32 1P068d8d24bcb7b852 0 2 0 1 32 1P0826c97833bb1d2c 0 2 0 1 30 1P0893750341d2d829 0 2 0 1 21 1P095320580fff2c1e 0 2 0 1 32 1P0a463a23f4e1238b 0 2 0 1 30 1P0a6428653be867c7 0 2 0 1 32 1P0a7d253adfd8ba2d 0 2 0 1 32 1P0a991bc57e3a0591 0 2 0 1 32 1P0a9c49dcfd7196aa 0 2 0 1 52 1P0aae94dcfc7b57d9 0 3 0 1 13 1 32 1P0ac13e49b6b288bf 0 2 0 1 32 1P0ae63c1c67d98828 0 2 1 1 33 1P0bb11c00bab20ebc 0 2 0 1 32 1P0c06f047147a1011 0 2 0 1 30 1P0cb9ef334649b2ef 0 2 0 1 32 1P0d60f2734c6960c3 0 3 0 1 32 1 50 1P0df5bdd599cc6ee4 0 2 0 1 32 1P0f2f7bc29bee66b3 0 2 0 1 52 1P0fcc84b3ab92325d 0 2 0 1 32 1P104624b7154c67c8 0 2 0 1 32 1P10dd98b91b2e96b1 0 2 1 1 33 1P1137a8ff9f387e5b 0 2 0 1 32 1P12471a2b7bb6426c 0 2 0 1 46 1P12616c94f2d42a93 0 2 0 1 32 1P129066a4cdd75793 0 2 0 1 32 1P12d5cba2c83f0451 0 2 0 1 32 1P130b9fc1b6bf9482 0 2 0 1 32 1P137a5007df0d12a9 0 2 0 1 32 1P14c41bfcd4060091 0 2 1 1 33 1P14cda8bb093588f3 0 2 0 1 32 1P158cbd9a3f2142a8 0 2 0 1 32 1P15e7187e5d69fd6b 0 3 0 1 17 1 32 1P1651a0a9b7222633 0 2 0 1 32 1P1705c58ee09a1744 0 2 0 1 32 1P1806f7765840777d 0 2 1 1 33 1P1a006a997c6c54d3 0 2 0 1 52 1P1a8f19586f05c516 0 2 0 1 32 1P1acdce6de575f3b8 0 2 0 1 32 1P1af9e0691cdec8b5 0 2 1 1 33 1P1bbab49dad922349 0 2 0 1 32 1P1bdfbca105ec8746 0 2 0 1 52 1P1cbed26e1b416901 0 2 0 1 48 1P1cca53b809f54ca9 0 2 0 1 42 1P1d31285ca76d03c4 0 2 0 1 32 1P1d96bb610f592178 0 2 0 1 13 1P1df4f6751fb61a76 0 2 0 1 32 1P1fa9589154f1be8e 0 2 0 1 30 1P1fdf9a0ca74d5581 0 2 0 1 32 1P1fe61c3019929a09 0 2 0 1 32 1P204d7b1e02b28c62 0 2 1 1 33 1P20958687d3f25186 0 2 0 1 32 1P2183fa66b6b777a0 0 2 0 1 52 1P22320ee415fe66b8 0 2 0 1 32 1P226b7fcc3753ffc0 0 2 0 1 52 1P22d01f3026135365 0 2 0 1 32 1P238cd99432c2df52 0 2 0 1 52 1P2508ab16f425d9ae 0 2 0 1 52 1P25357dd6f0d40176 0 2 0 1 32 1P258d395e21855027 0 2 1 1 33 1P264439e11a454db9 0 2 0 1 17 1P28a17f61a4811f8e 0 2 0 1 32 1P28c7a85d77241af6 0 2 0 1 32 1P28c7b20563a7431b 0 2 0 1 30 1P2908d8581cdb17a6 0 2 0 1 32 1P2a204be327bd7a0c 0 2 0 1 52 1P2a40aa309614e228 0 2 0 1 32 1P2bb145465ffef833 0 2 0 1 32 1P2bb17ef7bebf8f2e 0 2 0 1 32 1P2bf63bc974a920c8 0 2 0 1 30 1P2c8dba7400b682d4 0 3 0 1 17 1 32 1P2cb9302e7f4c748c 0 2 0 1 30 1P2d7e0f574dc2e0e1 0 3 1 1 49 1 50 1P2dd2b82372a885da 0 2 0 1 30 1P2de9282d8cce4d46 0 2 1 1 33 1P2e7cb76db913496a 0 2 1 1 33 1P2eb3422e59641d3f 0 2 1 1 33 1P2eb4fb7443db642b 0 2 0 1 22 1P30021c4df602f1fc 0 2 0 1 52 1P3012e136a29f2868 0 2 0 1 32 1P30650a2dd5ccad25 0 2 0 1 32 1P306637563733cdd9 0 2 1 1 33 1P30cb6d682fcb838b 0 3 1 1 49 1 50 1P3165622c6fe2a9d0 0 2 0 1 52 1P3238209ac6280aca 0 2 0 1 30 1P325c27aef56cabe1 0 2 0 1 30 1P32b60ce75b8c80d5 0 2 0 1 32 1P32fba82455098453 0 2 0 1 50 1P337bf0b4cbbe491f 0 2 1 1 33 1P337c6c45064f20af 0 2 0 1 30 1P341c5c4b04aa6398 0 2 0 1 22 1P360f52bfb6d668b2 0 2 0 1 52 1P373727a9643d9ee9 0 2 0 1 50 1P37fe1c5c94568c22 0 2 0 1 30 1P3927245e112eba54 0 2 0 1 52 1P3935e1530ad27585 0 2 1 1 33 1P39c5dae139e068ce 0 3 0 1 32 1 42 1P3a0207b2f8b9d37c 0 2 0 1 32 1P3a19e60c6d17b787 0 2 0 1 52 1P3b0abe2e50feb0ab 0 2 0 1 32 1P3c0f4d0aac05fc54 0 2 0 1 30 1P3c42e032ff58b586 0 2 1 1 33 1P3cf8035988305492 0 2 0 1 32 1P3da863fa15795f1a 0 2 0 1 32 1P3dec2c2c81d21a81 0 2 0 1 52 1P3fc8c1ed61c008af 0 2 0 1 30 1P3fca931741357f12 0 2 0 1 30 1N00762c4e0fcc73c0N00b4ea5e1caffaf6N00fed9d91c82f5c4N0404f8569ee23831N04ebb2f4ddd5f54dN04f06d4cb942ce18N0507af7f0df63bb4N050ab4f55f700a11N0640cf1f579b6c73N081bf47508765b8cN096115f6c72ad935N0c73b55b959f994aN0dfbae09c685a3d7N0e0e50b071ab225dN0e8892e94b55d674N0ecd6b05cf090497N10077b36f3281ddcN100e17dfad969f59N116c2621e773f45eN1208e5af7a9e97c5N1392dd9667e71c33N146ff55b965e9881N14bf6c522806c8e0N1586088c4c30370aN1613e980e3239817N17e8d85574480f4bN1805b1f8299bf9ceN1ab2a29c72e5278aN1ab9eb8cd606b77aN1cc97bdc01de8444N1d100f0a8ea0dd4eN1db1882024643e36N1ec2157367e94381N1fba77d2ea2c69ccN20e2fb020b1b4a0aN222892f8ec39a63aN2343c4530b9e0916N23a6b513fcc131d0N23cf8b49372ddbd5N23f3bc435f9e30dcN24554bb5b062b76aN24b22a30ca5866f0N27273e02c70b17d2N2b06902f27e4cc72N2be159e7e1ccaaa1N2c29dbf4acd2f674N2c70faa147b094a5N2d3797c98beeb92fN2ee20427b2a22168N2fde7bf76fbaf748N30e26fa34a7eaabaN3127f1d715e5208dN31cfcde792c9fd28N343c290c47163cb7N34a7059b27e95089N3510433b02969ba4N351405411594b611N36d0deb8a195b781N38efddd8ab4c2246N3bcf9e4025db1080N3c512d09d9b04848"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Ltac2 gd_tbl_AW_PfVsn () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_bytes"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.prefix_eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr_range"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.B.A_vsnp_num.ndig"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Walk.A_FMT_MEMADDR"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Lemma vsn_litloop : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn ()) "Plit,(0.(1.&8.))Pc,(1.&8.)Pp,$2.Pcnt,$2.PSPV,$2.PBUF,$2.Poff,$2.PE,$2.Pbs,(0.(1.&8.))Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps4,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(4.(1.&8.))Pm,P,(1.&40.)(4.(1.&8.))P,(5.$6.R25.(7.(1.&8.)R27.(8.(1.&8.)R26.(9.(1.&8.)))))P,Pb,(1.&8.)P,(:.(1.&8.)R1.R29.)(;.(<.(=.$2.(>.&8.R2.)+25.))(?.R2.))P,(10.+10000.R27.)P,(10.(11.(11.R28.(12.(13.(1.&8.)R2:.)))+1.)+65?000.)P,(10.+65?000.R27.)P,(14.$6.R6.(11.R28.+10.)(8.$15.(16.(17.&40.(11.R27.R26.)))(9.$15.)))P,(18.VCS,(11.R29.+10.)+8.)P,(10.(11.R2:.+18.)R29.)P,(19.$6.R9.R2:.R27.)P,(18.VCS,R2;.(12.(13.(1.&8.)R28.)))P,(1:.(11.R2<.(12.(13.(1.&8.)R29.)))(1;.+2.+3?.))P,(10.=R2<.)P,(10.(11.(11.R2>.R2=.)(12.(13.(1.&8.)R33.)))R2<.)P,(10.R2=.(11.R2?.(12.(13.(1.&8.)R2<.))))P,(10.=R32.)P,(1:.(11.R33.(12.(13.(1.&8.)R36.)))(1;.+2.+1?.))P,(1<.(8.(1=.$2.$2.)(1>.$2.$2.(11.R33.+10.)(11.R33.+18.))(8.(1=.$2.$2.)(1>.$2.$2.R32.(11.R32.(12.(13.(1.&8.)R2?.))))(9.(1=.$2.$2.))))R12.R11.)P,(1?.$6.R13.R12.)P,(20.$6.R13.)(21.$6.VAL,VCS,Lms',$22.(23.(1.&40.)La0',(1.&40.)(23.(1.&40.)La1',(1.&40.)(23.(0.(1.&8.))Lbs',(0.(1.&8.))(23.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))(;.(=.$22.R5.(24.(25.R36.(17.&40.R3;.)R35.R34.R33.R32.R31.R30.(17.&40.(11.R3<.(12.(13.(1.&8.)R3?.))))R4.R3.R2=.R2<.R2;.R2:.R29.R28.R27.(17.&40.R38.)R26.(17.&40.+25.)R25.R24.R23.R22.(17.&40.(11.R3=.(12.(13.(1.&8.)R3?.))))R21.R20.R1?.R1>.R1=.)R1<.(17.&40.+7=8:0.)R1;.(26.(1.&40.))R1.(27.$6.)))(;.(14.$6.R1.(11.R3;.+10.)(8.$15.(16.(17.&40.(11.(11.R3:.R39.)(12.(13.(1.&8.)R3?.)))))(9.$15.)))(;.(19.$6.R1.R3:.R2.)(;.(=.$28.(13.(1.&8.)R2.)(13.(1.&8.)R37.))(;.(29.R37.R2.R39.)(;.(2:.R2.R39.(11.R39.(12.(13.(1.&8.)R3?.))))(;.(1<.(8.(1=.$2.$2.)(1>.$2.$2.(11.R3;.+10.)(11.R3;.+18.))(8.(1=.$2.$2.)(1>.$2.$2.R3:.(11.R3:.(12.(13.(1.&8.)R37.))))(9.(1=.$2.$2.))))R1:.R1.)(;.(1?.$6.R1:.R1.)(20.$6.R1.)))))))))))))(24.(25.R31.(17.&40.R36.)R30.R2?.R2>.R2=.R2<.R2;.(17.&40.R37.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.(17.&40.R33.)R21.(17.&40.+25.)R20.R1?.R1>.R1=.(17.&40.R38.)R1<.R1;.R1:.R19.R18.)R17.(17.&40.+7=8:0.)R16.(26.(1.&40.))R14.(27.$6.)))")
(* [comment removed for export] *).
  Proof.
    induction lit as [|b lit IH]; intros until m; intros RO LIT PLO PHI SPLO CCH CRC CCB OUT CRB BH OFF ROOM EH CNT0 CNTH MU WM MI; al_facts.
    - apply evtA_done. cbn [length Z.of_nat]. rewrite !Z.add_0_r. eexists _, _, bs, m. split; [reflexivity|].
      split; [exact CCH|]. split; [exact OUT|]. split; [reflexivity|]. split; [apply prefix_eq_refl|]. split; [apply pr_range_empty|].
      split; [exact MU|]. split; [exact WM| exact MI].
    - cbn [length] in *. rewrite Nat2Z.inj_succ in *.
      destruct (LIT b (or_introl eq_refl)) as [B37 [B0 B27]].
      pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn [Z.pow Z.of_N Pos.pow] in BR.
      cbn [app] in RO. destruct RO as [ROB RO].
      pose proof (mem_inv_ro_read asegs m p b MI ROB) as RD1.
      assert (RD : ov_read_bytes asegs m (Z_to_bv 64 p) 1 = Some [b]).
      { rewrite ov_rdn. rewrite rdn_unfold. change (Z_to_bv 64 p) with (wa p). rewrite RD1. reflexivity. }
      zstep.
      zstep. if_falseU. zstep. if_falseU. zstep. zstep. if_falseU.
      destruct (out_store m BUF off bs b OUT ltac:(lia) ltac:(lia) BH MI) as (SOK & OUT1 & MI1 & WM1 & MU1).
      zstep.
      change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
      specialize (MU1 _ _ MU ltac:(cbn [inside]; right; left; lia)).
      apply (wmono_trans asegs _ _ _ WM) in WM1.
      apply (rw_cells_frame asegs m (SPV + 16) _ (BUF + off) [b]) in CCH; [| lia | cbn [length]; lia | cbn; lia].
      change (wa (BUF + off)) with (Z_to_bv 64 (BUF + off)) in *.
      set (m1 := write_to_mem m (Z_to_bv 64 (BUF + off)) [b]) in *; clearbody m1.
      clear SOK RD RD1.
      zstep. zstep. zstep. zstep. zstep.
      rewrite swrap32_id by lia.
      assert (LEN1 : length (upd bs (Z.to_nat off) b) = length bs) by apply upd_length.
      assert (PE1 : prefix_eq bs (upd bs (Z.to_nat off) b) off) by (apply prefix_eq_upd; lia).
      assert (PR1 : pr_range (upd bs (Z.to_nat off) b) off (off + 1)) by (apply pr_range_snoc; [apply pr_range_empty| lia| lia| split; assumption]).
      replace (BUF + off + 1) with (BUF + (off + 1)) in * by lia.
      eapply (evtA_mono asegs AL CS).
      { eapply (IH c (p + 1) (cnt + 1) SPV BUF (off + 1) E (upd bs (Z.to_nat off) b)); try rewrite LEN1; try eassumption; try lia.
        intros b' Hb'. apply LIT. right. exact Hb'. }
      cbn beta. intros ms' (a0' & a1' & bs' & m' & -> & CCH' & OUT' & LEN' & PE' & PR' & MU' & WM' & MI').
      eexists a0', a1', bs', m'.
      replace (cnt + 1 + Z.of_nat (length lit)) with (cnt + Z.succ (Z.of_nat (length lit))) by lia.
      replace (p + 1 + Z.of_nat (length lit)) with (p + Z.succ (Z.of_nat (length lit))) by lia.
      split; [reflexivity|].
      split; [replace (BUF + off + Z.succ (Z.of_nat (length lit))) with (BUF + (off + 1) + Z.of_nat (length lit)) by lia; exact CCH'|].
      split; [exact OUT'|]. split; [rewrite LEN'; exact LEN1|].
      split; [eapply prefix_eq_trans; [exact PE1| exact PE'| lia]|].
      split; [|split; [rewrite <- LEN1; exact MU'|split; [exact WM'| exact MI']]].
      intros k Hk; destruct (Z.eq_dec k off) as [->|NE]; [rewrite PE' by lia; apply PR1; lia| apply PR'; lia].
  Qed.

  Definition litok (b : byte) : bool := negb (bv_unsigned b =? 37) && negb (bv_unsigned b =? 0) && negb (bv_unsigned b =? 27).
  Lemma litok_all : forall lit, forallb litok lit = true -> forall b, In b lit -> bv_unsigned b <> 37 /\ pr b.
  Proof.
    intros lit H b Hb. rewrite forallb_forall in H. specialize (H b Hb). unfold litok in H.
    apply andb_true_iff in H. destruct H as [H H27]. apply andb_true_iff in H. destruct H as [H37 H0].
    apply negb_true_iff, Z.eqb_neq in H37, H0, H27. split; [exact H37| split; assumption].
  Qed.

  Lemma ndig_le2 : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn ()) "Pbase,$2.Pk,$28.Pj,$28.Pv,$2.P,(10.+2.R4.)P,(2;.#1.R3.)P,(;.(10.=R3.)(1:.R3.(1;.R6.(12.R4.))))(10.(2<.R7.R6.R4.)(12.R5.))")
(* [comment removed for export] *).
  Proof.
    intros base k; induction k as [|k IH]; intros j v Hb Hj Hv; cbn [ndig]; [lia|].
    destruct (Z.ltb_spec0 v base); [lia|].
    destruct j as [|j]; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia.
    assert (H : 0 <= v / base < base ^ Z.of_nat j) by nia.
    destruct j as [|j]. { exfalso. change (base ^ Z.of_nat 0) with (base ^ 0) in H. rewrite Z.pow_0_r in H. nia. }
    specialize (IH (S j) (v / base) Hb ltac:(lia) H). lia.
  Qed.

  (* [comment removed for export] *)
  Definition fmt_mem_lit : list byte := map (Z_to_bv 8) [109;101;109;111;114;121;32;97;116;32;97;100;100;114;101;115;115;32].
  Definition A_FMT_MEMADDR : Z := 0x1fc68.

  (* [comment removed for export] *)
  Theorem vsn_p_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfVsn ()) "Paddr,$2.PSP,$2.Plo,$2.PBUF,$2.Pn,$2.PVA,$2.Pbs,(0.(1.&8.))Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(4.(1.&8.))P,(;.(10.=R24.)(1:.R24.(1;.+2.+30.)))P,(;.(10.+22.R21.)(1:.R21.(1;.+2.+1?.)))P,(=.$2.(12.(13.(1.&8.)R20.))R22.)P,(2=.$6.R4.R25.R26.)P,(10.+65?000.R26.)P,(10.R27.(2>.R28.+1=0.))P,(18.VCS,R28.(2>.R29.R28.))P,(10.R2:.R28.)P,(19.$6.R9.R29.R26.)P,(18.VCS,R2:.R29.)P,(1:.(11.R2;.R2:.)(1;.+2.+3?.))P,(14.$6.R<.R2:.(8.$15.(16.(17.&40.R2?.))(9.$15.)))P,(18.VCS,R2;.+8.)P,(10.R30.R2<.)P,(2?.(10.(11.R2=.+8.)R2?.)(10.(11.R2?.R2>.)R2=.))P,(1:.(11.R2>.+8.)(1;.+2.+3?.))P,(20.$6.R11.)(21.$6.VAL,VCS,Lms',$22.(23.(1.&40.)La1',(1.&40.)(23.(1.&40.)La2',(1.&40.)(23.(1.&40.)La3',(1.&40.)(23.(1.&40.)La4',(1.&40.)(23.(1.&40.)La5',(1.&40.)(23.(1.&40.)La6',(1.&40.)(23.(1.&40.)La7',(1.&40.)(23.(1.&40.)Lt0',(1.&40.)(23.(1.&40.)Lt1',(1.&40.)(23.(1.&40.)Lt2',(1.&40.)(23.(1.&40.)Lt3',(1.&40.)(23.(1.&40.)Lt4',(1.&40.)(23.(0.(1.&8.))Lbs',(0.(1.&8.))(23.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))(;.(=.$22.R?.(24.(25.R3=.(17.&40.R43.)R3<.R3;.R7.R6.R5.R37.R36.(17.&40.+20.)R>.R=.R<.R;.R:.R9.R8.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R4.R3.R25.R24.)R23.(30.R3=.)R22.(26.(1.&40.))R1.(27.$6.)))(;.(2=.$6.R1.R42.R43.)(;.(19.$6.R1.R41.R2.)(;.(=.$28.(13.(1.&8.)R2.)(13.(1.&8.)R3>.))(;.(14.$6.R1.R3?.(8.$15.(16.(17.&40.R44.))(9.$15.)))(;.(1<.(8.(1=.$2.$2.)(1>.$2.$2.R42.R43.)(8.(1=.$2.$2.)(1>.$2.$2.R41.(11.R41.R40.))(9.(1=.$2.$2.))))R21.R1.)(;.(1?.$6.R21.R1.)(20.$6.R1.))))))))))))))))))))))(24.(25.R2>.(17.&40.R34.)R2=.R2<.R2;.R2:.R29.R28.R27.(17.&40.R32.)(17.&40.R31.)(17.&40.$31.)(17.&40.R30.)R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(17.&40.+7=810.)R13.(26.(1.&40.))R12.(27.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros Haddr Hn LEN ST LOIMG SPL SCS SPB OUT CRB BH VAC CRV SPVA VAB VAH MI. al_facts.
    pose proof (munch_refl [(lo, SP); (BUF, BUF + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_FMT_MEMADDR. destruct OUT as [OUTb OUTw].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7d8a0] [] 60%N).
    (* [comment removed for export] *)
    lazymatch goal with FRl : rw_cells _ ?mx (SP + -128) _, STl : stk _ _ lo (SP + -128), BYl : bytes_at _ _ BUF bs, WMl : wmono _ m _ |- _ =>
      chunk_split FRl 2%nat FRa FRr; chunk_split FRr 1%nat CCH FRb;
      replace (SP + -128 + 16 + 8) with (SP + -104) in FRb by (clear; lia);
      replace (Z_to_bv 64 BUF) with (Z_to_bv 64 (BUF + 0)) in CCH by (f_equal; clear; lia);
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw WMl) : u8arr asegs mx BUF bs) as OUTl; clear BYl; try clear LXlen end.
    replace (BUF + (n + -1)) with (BUF + n + -1) by (clear; lia).
    assert (ROF : ro_bytes asegs 130152 (fmt_mem_lit ++ [Z_to_bv 8 37])) by (apply ro_bytes_b_sound; vm_compute; reflexivity).
    assert (CRC : crange CS (SP + -128 + 16) 8) by (intros x Hx; apply SCS; clear -Hx SPL; lia).
    eapply (evtA_cut asegs AL CS).
    { eapply (vsn_litloop fmt_mem_lit (Z_to_bv 8 37) 130152 0 (SP + -128) BUF 0 (BUF + n + -1) bs);
        first [ exact ROF | exact CCH | exact CRC | exact OUTl | apply munch_refl | apply wmono_refl | assumption
              | apply litok_all; vm_compute; reflexivity
              | rewrite LEN; exact CRB
              | cbn [length fmt_mem_lit map]; clear -Hn LEN SPL SPB LOIMG BH; lia ]. }
    cbn beta. intros ms' (a0l & a1l & bs1 & m2 & -> & CCH1 & OUT1 & LEN1 & PE1 & PR1 & MUc & WMc & MIc).
    rewrite LEN in MUc. clear CCH OUTl.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx m2 MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    change (Z.of_nat (length fmt_mem_lit)) with 18 in *. change (0 + 18) with 18 in *. change (130152 + 18) with 130170.
    replace (BUF + 0 + 18) with (BUF + 18) in CCH1 by (clear; lia). replace (SP + -128 + 16) with (SP + -112) in * by (clear; lia).
    assert (LB1 : Z.of_nat (length bs1) = n) by (rewrite LEN1; exact LEN).
    destruct OUT1 as [OUT1b OUT1w].
    (* [comment removed for export] *)
    assert (FMTC : ro_cells asegs m2 130152
      [C1 (Z_to_bv 8 109); C1 (Z_to_bv 8 101); C1 (Z_to_bv 8 109); C1 (Z_to_bv 8 111); C1 (Z_to_bv 8 114); C1 (Z_to_bv 8 121); C1 (Z_to_bv 8 32);
       C1 (Z_to_bv 8 97); C1 (Z_to_bv 8 116); C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 97); C1 (Z_to_bv 8 100); C1 (Z_to_bv 8 100); C1 (Z_to_bv 8 114);
       C1 (Z_to_bv 8 101); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 115); C1 (Z_to_bv 8 32); C1 (Z_to_bv 8 37); C1 (Z_to_bv 8 112); C1 (Z_to_bv 8 0)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MIc| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    assert (JTC : ro_cells asegs m2 150176 [C4 (Z_to_bv 64 364832)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MIc| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    (* [comment removed for export] *)
    lx_run (PLAN [0x7db74] [] 60%N).
    (* [comment removed for export] *)
    assert (OUTw1 : wr_at asegs m BUF (Z.of_nat (length bs1))) by (rewrite LEN1; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs1, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw1 WMl) : u8arr asegs mx BUF bs1) as OUT2; clear BYl OUT1b OUT1w OUTw1; try clear LXlen end.
    clear FMTC JTC.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8arr_store_ok asegs mx BUF bs1 18 (Z_to_bv 64 (BUF + 18)) OUT2 ltac:(clear -LB1 Hn; lia) eq_refl) as SOK end.
    zstep. rewrite (le1_lit 48) by (clear; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u8arr_write asegs mx BUF bs1 18 (Z_to_bv 8 48) OUT2 ltac:(clear -LB1 Hn; lia)) as OUT3 end.
    store_done. try clear SOK.
    set (bs2 := upd bs1 (Z.to_nat 18) (Z_to_bv 8 48)) in *.
    assert (LB2 : Z.of_nat (length bs2) = n) by (unfold bs2; rewrite upd_length; exact LB1).
    zstep. zstep. zstep. if_falseU. zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (u8arr_store_ok asegs mx BUF bs2 19 (Z_to_bv 64 (BUF + 18 + 1)) OUT3 ltac:(clear -LB2 Hn; lia) ltac:(f_equal; clear; lia)) as SOK end.
    zstep. rewrite (le1_lit 120) by (clear; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u8arr_write asegs mx BUF bs2 19 (Z_to_bv 8 120) OUT3 ltac:(clear -LB2 Hn; lia)) as OUT4 end.
    store_done. try clear SOK.
    set (bs3 := upd bs2 (Z.to_nat 19) (Z_to_bv 8 120)) in *.
    assert (LB3 : Z.of_nat (length bs3) = n) by (unfold bs3; rewrite upd_length; exact LB2).
    lx_clear_mem m2.
    (* [comment removed for export] *)
    destruct OUT4 as [OUT4b OUT4w].
    lx_run (PLAN [0x7e118] [] 30%N).
    assert (LL : Z.max (ndig 16 20 addr) 12 = 12).
    { pose proof (ndig_le2 16 20 12 addr ltac:(clear; lia) ltac:(clear; lia) ltac:(change (16 ^ Z.of_nat 12) with (2^48); clear -Haddr; lia)) as NDL.
      pose proof (ndig_ge1 16 20 addr) as NDG. clear -NDL NDG. lia. }
    assert (OUTw3 : wr_at asegs m BUF (Z.of_nat (length bs3))) by (rewrite LB3, <- LEN; exact OUTw).
    lazymatch goal with FRl : rw_cells _ _ (SP + -128) _ |- _ =>
      chunk_split FRl 2%nat FRa2 FRr; chunk_split FRr 1%nat CCl FRb2; replace (SP + -128 + 16 + 8) with (SP + -104) in FRb2 by (clear; lia);
      replace (SP + -128 + 16) with (SP + -112) in CCl by (clear; lia) end.
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs3, WMl : wmono _ m ?mx', STl : stk _ _ lo (SP + -128), CCl : rw_cells _ _ (SP + -112) _ |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw3 WMl) : u8arr asegs mx BUF bs3) as OUT5; clear BYl OUTw3; try clear LXlen;
      replace (BUF + (n + -1)) with (BUF + n + -1) by (clear; lia);
      eapply (evtA_cut asegs AL CS);
      [ eapply (apn_spec AL IMG ALWF CS CSOK addr 16 12 1 0 (SP + -128) lo (SP + -112) BUF 20 (BUF + n + -1) bs3);
          first [ exact STl | exact CCl | exact OUT5 | exact CRC | assumption
                | rewrite LB3; exact CRB
                | right; reflexivity
                | rewrite ?LL, ?LB3; clear -Haddr Hn SPL SPB LOIMG BH; lia
                | intros x Hx; apply SCS; clear -Hx SPL; lia ]
      | ] end.
    cbn beta. intros ms' (a1n & a2n & a3n & a4n & a5n & a6n & a7n & bs4 & m3 & -> & ST3 & CCH3 & OUT6 & LEN4 & PE4 & PR4 & MUc & WMc & MI3).
    rewrite LL in *. rewrite LB3 in MUc. clear OUT5.
    lazymatch type of MUc with munch _ ?mx _ => transport_after_call asegs mx m3 MUc WMc; clear MUc WMc; lx_clear_mem mx end.
    ret_lit.
    assert (LB4 : Z.of_nat (length bs4) = n) by (rewrite LEN4; exact LB3).
    destruct OUT6 as [OUT6b OUT6w].
    (* [comment removed for export] *)
    lx_run (PLAN [0x7dc60] [] 30%N).
    lx_clear_mem m3.
    (* [comment removed for export] *)
    assert (OUTw4 : wr_at asegs m BUF (Z.of_nat (length bs4))) by (rewrite LB4, <- LEN; exact OUTw).
    lazymatch goal with BYl : bytes_at _ ?mx BUF bs4, WMl : wmono _ m ?mx' |- _ =>
      pose proof (conj BYl (wr_at_transport _ _ _ _ _ OUTw4 WMl) : u8arr asegs mx BUF bs4) as OUT7; clear BYl OUTw4; try clear LXlen;
      pose proof (u8arr_store_ok asegs mx BUF bs4 32 (Z_to_bv 64 (BUF + 32)) OUT7 ltac:(clear -LB4 Hn; lia) eq_refl) as SOK end.
    zstep. rewrite (le1_lit 0) by (clear; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx _ _) _) =>
      pose proof (u8arr_write asegs mx BUF bs4 32 (Z_to_bv 8 0) OUT7 ltac:(clear -LB4 Hn; lia)) as OUT8 end.
    store_done. try clear SOK.
    destruct OUT8 as [OUT8b OUT8w].
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 30%N).
    assert (OUTw5 : wr_at asegs m BUF (Z.of_nat (length (upd bs4 (Z.to_nat 32) (Z_to_bv 8 0))))) by (rewrite upd_length, LB4, <- LEN; exact OUTw).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, BYl : bytes_at _ _ BUF _ |- _ =>
      apply evtA_done; lx_exs; lx_ands;
      [ lx_mseq
      | assumption
      | exact (conj BYl (wr_at_transport _ _ _ _ _ OUTw5 WMl))
      | rewrite upd_length, LEN4; unfold bs3, bs2; rewrite !upd_length; exact LEN1
      | assumption | exact MUl | exact WMl | assumption ] end.
  Qed.
End Walk.
