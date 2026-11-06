(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.zstd.huf_decompress.images Require Import Asan.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib
  AsanAcct AsanAcctShape AsanAcctImages.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanNodesAux AsanStartLoops AsanNodesStartX AsanNodesStartXInit Asan_code_startx.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanNodesStartXAsan () := "I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib2AS<AsanNodesAux9fetch_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallK47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C59OSSVerify5KrLib2ASCAsanNodesStartXInitDinit_x_sound_envscanC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib2AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib2AS>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4ASANC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanPlanImages3APHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanPlanImages7asan_wxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanPlanImages<asan_in_hullC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanPlanImages<asan_hull_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e890C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e894C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e898C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e890C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e894C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e898C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgGTgt_huf_decompress_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e890C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e894C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e898C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2ASCAsanNodesStartXInitCinit_x_sound_pnscanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e94cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7W_9e95cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e94cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7D_9e95cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e94cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS@Asan_code_startx7F_9e95cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanInit5argH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?AsanNodesStartX>x_sound_layoutC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanInit5SINV0C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib2AS8AsanInit;SINV0_frameC1?~~~~~~~~~~~~~~~K47Corelib4Init5Peano2le01c59OSSVerify5KrLib2ASCAsanNodesStartXAsanNnode_x_sound_XEnvScan_asan_genC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS:AxSymExec33AX23env00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanInit;SINV0_agreeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2ASCAsanNodesStartXAsanMnode_x_sound_XPnScan_asan_genC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section AsanInstance.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable LIMIT : Z.

  Section AnySINV.
    (* [comment removed for export] *)
    Variable SINV : env -> (word -> option byte) -> Prop.
    Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
    Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
    (* [comment removed for export] *)
    Variable nx0 : nat.
    Hypothesis Hnx0 : (NX0 <= nx0)%nat.
    Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

    Theorem node_x_sound_XEnvScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesStartXAsan ()) ["AsanInstance"; "AnySINV"] "h02Hah14Hnx1h27__arithh34__ffh46__sat1h56__sat2h68__varmaph75__with84cstrh95cstr0p;2p;1p;4p;3p;6p;<p;7p;Sg0000R0j2_Tg000JR1j1HTg000jR2j2DTg001Fj25Tg001`j4UTg002Gj1FTg002lj12Tg003Qj14Tg003oj2ITg004Wj2:Tg0053j2]Tg005Pj3\Tg0064j1VTg006Tj1TTg0074j1STg007Rj1RTg0080j1QTg008[j28Tg009>j4<Tg009ij17Tg00:Nj3NTg00;1j1MTg00;Oj3LTg00<2j2KTg00<Tj3JTg00=3j4OTg00=ej2PTg00>Bj3ETg00>\j2?Tg00?7j3>Tg00?Zj2=Tg00@Dj6@Tg00ABj1BTg00BBj4GTg00B]l<WTg00CBj7XTg00Cfj7YTg00DJlSZTg00EZg00F9R3P0P1P2g00FWg00G9R2f4R1f3R0f2R4f1R5f0R6M<Wp=^g00H0R7/D6p=6%26#2p=1%26#7p=3%76#7p=9%76#2p=0P5g00HNR8g00HmR9P9g00IMR:P6g00ImFXp=;P4P8P9P9P:P5P6FYp=Cg00JMR9g00JmR87E6p=Ag00KMg00LIg00MAg00N;g00O9g00P<g00Q?R;g00R?R<g00S?R=P6P5P4P0P1g00T?g00U?g00V?f5f6f7f8f9f:f;f<f=f>f?f@fAfBfCfDfEfFMSZp=[p,3nx0R1,_2%H2R0%H1R>'DR?P01530P1P>153>D^p,4Hnx0R@CUP?%F1%6>%F2%60g00W?R0#2R2#4R>%22#1#1R2#4R?'I1:7>%6?1]>?RA,:7[[%6>RBg00WdRCA\>?5UW0%6A\C^0Bg00X@RB#V%TB%S3%R3%Q3RBP31837g00Xl%20#3#9#0#0#1#3#0#1#1#4RC,83R?C<,;BP3%70#1#4RD,839N3?R?g00YS183>%M2R25L3C<,;BP3%20#3#9#0#0#1#3#0#9#1#4R>,83g00Z:P?C<,;B5CB3C1KB:P6P4g00Za,59AJ375COb3b6b7%6C1PCDRD/:AAE3>D'?'?P6b2b4b5b9b8b1g00[AR6g00\PRD9>2CRC,=2R>PCP;153>g00\lE@P6%20#3#9#0#0#1#3#0#3#1#4=>2DR>,=2RCP>P<153Cg00]lE@P6%20#3#9#0#0#1#3#0#0#1#4=>2DRD,=2R2PDP=1532g00^lE@%B;#A%B<#AR<%B=#AR='?1598R8P<P=P8P8CGCGp,2spp,5rdrawp,4brk0p,4argvp,4envpp,3FS0p,3Hspp,3Hvap,3Hvep,3uidp,2hwp,4Hfitp,4SINVp,:SINV_SINV0p,:SINV_frameP1P@p,5LIMITMG[o"). Qed.

    Theorem node_x_sound_XPnScan_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesStartXAsan ()) ["AsanInstance"; "AnySINV"] "h02Hah14Hnx1h27__arithh34__ffh46__sat1h56__sat2h68__varmaph75__with84cstrh95cstr0p;2p;1p;4p;3p;6p;<p;7p;Zg0000R0j2_Tg000JR1j1HTg000jR2j27Tg001`j4UTg002Gj1FTg002lj13Tg003Qj14Tg003oj2LTg004Wj2BTg0053j2ITg005Pj3]Tg0064j1\Tg006Tj1VTg0074j1TTg007Rj1STg0080j1RTg008[j29Tg009>j4CTg009ij1>Tg00:Nj3QTg00;1j1PTg00;Oj3OTg00<2j2NTg001Fj2ATg00<Tj3KTg00=3j4MTg00=ej2JTg00>Bj3GTg00>\j2<Tg00?7j38Tg00?Zj2=Tg00@Dj6:Tg00ABj1?Tg00BBj4@Tg00B]l<WTg00CBj7XTg00Cfj7YTg00_llZZTg00F9R3f0R4'Ap=6g00EZP3P0P1P2g00FWg00G9R2f4R1f3R0f2R5f1R6P4M<Wp=^%34#3p=0%34#>p=2%>4#>p=5%>4#3p=1P6g00HNR7g00HmR8P8g00IMR9P4g00ImFXp=DP5P7P8P8P9P6P4FYp=Eg00JMR8g00JmR77G4p=;g00KMg00LIg00MAg00N;g00O9g00P<g00a;R:g00b;R;g00c;R<g00d;R=g00e;R>P4P6P5P0P1f5f6g00f;g00g;g00h;g00i;g00j;f7f8f9f:f;f<f=f>f?f@fAfBfCfDfEfFfGfHfIMZZp=[p,3nx0R1,_2%H2R0%H1R?'7R@P0%60P1P?%6?D^p,4Hnx0RACUP@%F1g00H0R@/7?%F217@0g00W?R0#3R2#4R?%02R2#3#0RB#4RC'L1B@?17@C1I?CRD,B@[[17@?REg00WdRFA]?C6UW017@D\F^0Eg00X@RE#\%VE%T3%S3%R3REP3%42R2,93g00Xl%30#2#5#1#1#2#0#1#2#0#4RF,93RCCC,DEP3%>0#0#4RG,939Q3CRCg00YS193?%PBRB5O3CC,DEP3%30#2#5#1#1#2#0#5#0#0#4R?,93g00Z:PCCC,DE5EE3E1NE9P4P5g00Za,A8AK3@6CMb3b6b7172F1JFGRG/BDAG3?G'<'<P4b2b4b5b9b8b1g00[AR4%30#2#5#1#1#2#0#2#5#0#4g00\PRG58BR?,=BR3P?P:%63g00k;E:P4%30#2#5#1#1#2#0#1#0#0#4=8BGR3,=BR?P3P;%6?g00l;E:P4A8BFGRF,=BR?PFP<%6?g00m;E:P4%30#2#5#1#1#2#0#1#1#0#4=8BGR?,=BRFP?P=%6Fg00n;E:P4%30#2#5#1#1#2#0#1#5#0#4=8BGRG,=BRBPGP>%6Bg00o;E:%?:#;%?;#;R;%?<#;R<%?=#;R=%?>#;R>'<R:'<RB'<1A87R7P;PBP7P<P:P7P=P>P7P7C@C@C@C@p,2spp,5rdrawp,4brk0p,4argvp,4envpp,3FS0p,3Hspp,3Hvap,3Hvep,3uidp,2hwp,4Hfitp,4SINVp,:SINV_SINV0p,:SINV_frameP1PAp,:SINV_agreep,5LIMITMJ[o"). Qed.

    Theorem node_x_sound_XLayout_asan_gen : x_stmt ASEGS ASAN nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesStartXAsan ()) ["AsanInstance"; "AnySINV"] "p;7g010;j71Tg0111j70Tg00KMg00LIp,3nx0p,5LIMITp,4SINVg00MAp,2spp,5rdrawp,4argvp,4envpp,3uidp,2hwF1p,3FS0F0o"). Qed.
  End AnySINV.

  (* [comment removed for export] *)
  Theorem node_x_sound_XEnvScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XEnvScan.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesStartXAsan ()) ["AsanInstance"] "h01Eh11Hh21Mp;8p;1p;:p;5g0127j88l:6Tg002lj10Tg00;1j12Tg012mj11Tg013Pj17Tg0142j84Tg014nj13Tg015Hj55Tg00MAR0p,2spR1p,5rdrawR2p,4brk0R3p,4argvR4p,4envpR5p,3uidR6p,2hwR7G8g016bg00W?#0#0#0R8#0#0#0#2#1%28#1#7[P0P1P2P3P4P5P6P7f1f0R8M:6P8W1W2W0P0P1P2P3P4P5P6P7G4g00G9R7%37D5o"). Qed.

  Theorem node_x_sound_XPnScan_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XPnScan.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesStartXAsan ()) ["AsanInstance"] "h01Eh11Hh21Mp;8p;1p;:p;6g0127j89l:7Tg002lj10Tg00;1j12Tg012mj11Tg013Pj18Tg0142j84Tg014nj13Tg017^j85Tg018Zj66Tg00MAR0p,2spR1p,5rdrawR2p,4brk0R3p,4argvR4p,4envpR5p,3uidR6p,2hwR7G9g016bg00W?#0#0#0R8#0#0#0#2#1%28#1#8[P0P1P2P3P4P5P6P7f1f0R8M:7P8W1W2W0P0P1P2P3P4P5P6P7G4g00G9R8%38P0P1P2P3P4P5P6P7G5E6o"). Qed.

  Theorem node_x_sound_XLayout_asan :
    x_stmt ASEGS ASAN NX0 LIMIT (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) FS0 XLayout.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesStartXAsan ()) ["AsanInstance"] "p;8p;7g0127j82Tg010;j71Tg0111j70Tg00KMg00LIg00G9p,5LIMITg00MAR0p,2spR1p,5rdrawR2p,4brk0p,4argvR3p,4envpR4p,3uidR5p,2hwR6G2P0P1P2P3P4P5P6F1p,3FS0F0o"). Qed.
End AsanInstance.
