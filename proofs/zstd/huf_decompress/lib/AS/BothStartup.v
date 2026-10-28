(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 BothPlanImages AsanInit
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsBothClose AsanNodesStartX AsanNodesStartXBoth AsanMaxVA AsanNodesMaxVA AsanNodesWJoin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanStartup () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01I6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS5cs_ok00C6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS6alwaysI47Corelib4Init5Logic2eq00c5ARocqVerifyHarness?AgentSubmission2AS;BothStartup3XN0K47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission2AS9AxSymRun39env_agreeC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP3nxtI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP2pcC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS6cfg_ofI5ARocqVerifyHarness?AgentSubmission2AS7SpinAlg9srealizes00C47Corelib4Init5Logic9False_indC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS:node1_stmtC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS8ext_stmtI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP6atable00I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00I6ARocqVerifyHarness?AgentSubmission2AS:AxSymExec33AX23env00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I6ARocqVerifyHarness?AgentSubmission2AS:AxSymExec33AX24expr00I6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP3acs00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission2AS8ShapeAlg4TSetK47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00c5ARocqVerifyHarness?AgentSubmission2AS;BothStartup3XE0K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01C6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS2WpC5ARocqVerifyHarness?AgentSubmission2AS8ShapeAlg6t_emitC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS9emit_stmtI6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP6spiece00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00c5ARocqVerifyHarness?AgentSubmission2AS;BothStartup3XB0C5ARocqVerifyHarness?AgentSubmission2AS8ShapeAlg6t_alt2C6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS9ext2_stmtK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidableEbool_decide_eq_true_1C47Corelib5Lists7ListDef3nthC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP7x_maxvaC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC35stdpp9decidable;bool_decideC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA;MAXVA_WORDSC5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W0C5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages5ASEGSC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W1C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W2C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W3C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W4C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W5C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W6C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W7C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W8C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA2W9C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W10C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W11C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W12C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W13C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W14C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W15C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W16C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W17C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W18C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W19C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W20C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W21C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W22C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W23C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W24C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W25C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W26C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W27C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W28C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W29C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W30C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W31C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W32C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W33C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W34C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W35C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W36C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W37C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W38C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W39C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W40C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W41C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W42C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W43C5ARocqVerifyHarness?AgentSubmission2AS9AsanMaxVA3W44K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP4BOTHC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission2AS8AsanInit:argH0_highC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit5argH0C45stdpp9bitvector;definitions;bv_unsignedC6ARocqVerifyHarness?AgentSubmission2AS:AxSymExec33AX22evC6ARocqVerifyHarness?AgentSubmission2AS:AxSymExec33AX22ebI47Corelib4Init5Peano2le00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission2AS8AsanInit;argH0_agreeC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS6x_stmtC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseJasan_node_x_sound_XIMemsetC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseJasan_node_x_sound_XIMemcpyC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseIasan_node_x_sound_XMemsetC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseIasan_node_x_sound_XMemcpyC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseLasan_node_x_sound_XMemIsZeroC5ARocqVerifyHarness?AgentSubmission2ASCAsanNodesStartXBothNnode_x_sound_XEnvScan_asan_genC5ARocqVerifyHarness?AgentSubmission2ASCAsanNodesStartXBothMnode_x_sound_XPnScan_asan_genC5ARocqVerifyHarness?AgentSubmission2AS?AsanNodesStartX>x_sound_layoutC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseKasan_node_x_sound_XIStrncpyC5ARocqVerifyHarness?AgentSubmission2AS=SumsBothCloseJasan_node_x_sound_XPopFreeC5ARocqVerifyHarness?AgentSubmission2AS>AsanNodesMaxVA=x_sound_maxvaC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP3NX0C56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages7asan_wxC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages<asan_in_hullC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages<asan_hull_okc5ARocqVerifyHarness?AgentSubmission2AS;BothStartup@asan_maxva_rangec5ARocqVerifyHarness?AgentSubmission2AS;BothStartup?asan_maxva_codeC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages3APHC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP4CEILK46Stdlib9micromega:ZMicromega;ZArithProof01I6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5xnode00I5ARocqVerifyHarness?AgentSubmission2AS8AsanInit9img_facts00C5ARocqVerifyHarness?AgentSubmission2AS8AsanInit2R0C6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP7a_entryC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit5FULL0C5ARocqVerifyHarness?AgentSubmission2AS8AsanInit6model0C5ARocqVerifyHarness?AgentSubmission2AS8AsanInit2E0C6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS2sdC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit:init_cs_okC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit5SINV0C6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP;init_acs_ofK47Corelib4Init5Peano2le01C5ARocqVerifyHarness?AgentSubmission2AS>AsanNodesWJoin3XNSC5ARocqVerifyHarness?AgentSubmission2AS<AsanNodesMmB?node_exit_soundc5ARocqVerifyHarness?AgentSubmission2AS;BothStartupEasan_node_x_sound_allC5ARocqVerifyHarness?AgentSubmission2AS>AsanPlanSound2?node_join_soundc5ARocqVerifyHarness?AgentSubmission2AS;BothStartup9XE0_soundc5ARocqVerifyHarness?AgentSubmission2AS;BothStartup9XB0_soundC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit3inpC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC56Stdlib6ZArith6BinInt1Z4of_NC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit;init_cfg_eqC5ARocqVerifyHarness?AgentSubmission2AS<AsanNodesMmB>node_sys_soundC5ARocqVerifyHarness?AgentSubmission2AS<AsanNodesMmB?node_brk2_soundC5ARocqVerifyHarness?AgentSubmission2AS<AsanNodesMmADnode_mmap2_sound_OBLC5ARocqVerifyHarness?AgentSubmission2AS<AsanNodesMmAEnode_mmapin_sound_OBLC5ARocqVerifyHarness?AgentSubmission2AS<AsanNodesMmAHnode_mprotect2_sound_OBLC5ARocqVerifyHarness?AgentSubmission2AS>AsanNodesWJoin9XNS_soundC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS;check_soundC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages<asan_res_lenC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages>asan_shadow_okC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages=asan_res_hullC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages=asan_hull_covC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP9both_initC5ARocqVerifyHarness?AgentSubmission2AS8ShapeAlg5t_nilC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages>asan_img_factsI4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP7loopctx00C5ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_both1M7init_pc".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Lemma XN0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext_stmt SEGS A nx0 LIMIT XN0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs cs' E R FULL model T _ _ H. discriminate H. Qed.
Lemma XE0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, emit_stmt SEGS A nx0 LIMIT XE0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : forall SEGS A nx0 LIMIT SINV argH FS0, ext2_stmt SEGS A nx0 LIMIT XB0 SINV argH FS0.
Proof. intros ? ? ? ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma asan_maxva_code : forall i, (i < 45)%nat ->
  fetch_word ASEGS (Z_to_bv 64 (x_maxva BOTH + 4 * Z.of_nat i)) = Some (nth i MAXVA_WORDS W0).
Proof.
  intros i Hi. cbn [x_maxva BOTH].
  do 45 (destruct i as [|i];
    [cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add nth MAXVA_WORDS];
     lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end |]).
  exfalso. lia.
Qed.

Lemma asan_maxva_range : 0 < x_maxva BOTH /\ x_maxva BOTH + 180 < 2 ^ 64.
Proof. cbn [x_maxva BOTH]. lia. Qed.

(* [comment removed for export] *)
Section XAll.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variable FS0 : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid hw : word.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Hypothesis SINV_SINV0 : forall E M, SINV E M -> SINV0 APH sp rdraw brk0 argv envp uid hw E M.
  Hypothesis SINV_frame : forall E M M', (forall a, argH0 APH sp rdraw argv envp uid hw E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  (* [comment removed for export] *)
  Variable nx0 : nat.
  Hypothesis Hnx0 : (NX0 <= nx0)%nat.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  (* [comment removed for export] *)
  Variable LIMIT : Z.

  Theorem asan_node_x_sound_all : forall x, x_stmt ASEGS BOTH nx0 LIMIT SINV (argH0 APH sp rdraw argv envp uid hw) FS0 x.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartup ()) ["XAll"] "p'0h01nh11Eh21ah32E'h44__x1h54__x2h64__x3h72AAh82AHh91Hh:3Hagh;2Hbh<2Hnh=3Hn0h>4Hnx1h?7__arithh@4__ffhA8__varmaphB5__withC4cstrhD5cstr0hE5cstr1hF1xi001xp;9p;1p;3p;2p;4p;;p;7p;8p;Bp;Cp;<p;=g01\cl9mTg003nj12Tg004Sj1BTg0051j1@Tg01]^l94j7bTg008\j30Tg01^Tj2UTg00^RR0j23Tg00:kj3QTg00W_R1j27Tg01_>j21Tg003Nj1ETg01`7j15Tg00XUR2j16Tg00\jR3j29Tg00Zoj28Tg00]Fj4GTg01a0R4j2TTg00]mj1=Tg00W@j1DTg01aJj2<Tg01b3j3CTg01b\j2PTg00OGj1OTg01cHj3NTg00^nj2ATg01chj4MTg00_Lj1LTg00_jj1KTg0066j1JTg00a8j2;Tg00a[j4:Tg00bFj1ITg00cLj2HTg00cnj2STg00dZj3lTg00e9j4kTg01dFj4jTg01e1j4fTg01eLl;eTg01fHj8ZTg01gHl9[Tg01hXl9\Tg01ihl9XTg01k7l9]Tg01lFl9^Tg01mXlB_Tg01o2lC`Tg020Kj7aTg021Ql9VTg022bl9cTg00iQl<?Tg00j6j7gTg00k=j8hTg0242l=iTg00E<R5g00E[R6P1P2P3g00o2R7f5R8f4R9f3R:f2R;f1R<f0R=M<?p=YP5P6P1P2P3P7P9P:P;g0256R7P<P=M<?p=WP5P6P4P2P0g025mP7P9P:P;P<P=M<?p=RP<g00oTR0g0103R2P2g010SR4P=g0113Fgp=>P:P0P2P2P4P;P<P=Ghp=Fg00mRR0g01X]R3P8P9P:P;P<g026Og027Mg028PP=g029Sg02:WM=ip=dg02;ZR1p,2spR>p,5rdrawR?p,4argvR@p,4envpRAp,3uidRBp,2hwRCp,3HspRDp,3HvaREM9mg00F9RFg00G5RG#2RH#2#2RI#2#2#2#BRJ#@RKg00GZRLP1P>P?P@PAPBPCP<P=M94g00K[RM30g02<T1UJ<'3[]2]1p,3nx0RJ?Q;<RNg00<]17=JRO118<119<50K[^05%BI#@#E\5RI%5:%5;30P1P>P?P@PAPBPCP9P;M94P1P>P?P@PAPBPCP:P;M9450LP=f7RP/1<f6RQ/1<50K\O^05%5QRO%5850IP1P>P?P@PAPBPCPPPQP817=7RQf9/1<f8/1<50K[^05%5P=0IOP:P<17<J%6<RO%6JRI'9P<PO186ORRPJPI186IRSEY17<7%67RT,9ORUP<POPRPT186TRRDWP=CGPU1T7J13TIRUPTPRPJPIPSDRp,4Hnx0RSCGPU%=:g01VERU%6:'3%=J13UI%=713UTg01VcR7g011SRR#DRO#D,<61<6O1<6R5C65C6g02=L'P%O73N%E7P61A6;P<1A6:CM%L6%K6R7P6%JG,;6RRg01WO1;6HRHC:,>7%I2R2P7P61;6GRGg01X6ROPRC:,>7P2P6PGPOPHC:,>7CFCF1H74P=P;18LM1S=;=0LMdAl6U<Ckb@bAbBX46X56X6613;<19<:19;:[[^46^56^66P=PTPI%6PP9P8O5b?bEbDbCb>b=CjO2X<QX05P=CfM;eW;W:P<P=O2n2001000000121000000W9X2KX3FX1FP1P>P?P@PAPBPCP:P<M94P1P>P?P@PAPBPCP;P<M9450L\N^2K^3F^1Fg02>8RFPFP0P3PJp,5LIMITRFp,4SINVRKP1P>P?P@PAPBPCFbR1p,3FS0RNP=GZP=PJPFPKP1P;P<p,:SINV_frameR=p,:SINV_agreeRLPNM9[PJPFPKP1P;P<P=PLPNM9\PJPFPKP1P;P<P=PLPNM9XPJPFPKP1P;P<P=PLPNM9]PJPFPKP1P;P<P=PLPNM9^P>P?p,4brk0R:P@PAPNPDPEp,3HveR5PBPCp,4HfitRQPFPKp,:SINV_SINV0R8P=PJPSMB_P>P?P:P@PAPNPDPEP5PBPCPQPFPKP8P=PJPSPLMC`P0P3PJPFPKP1PNFaPJPFPKP1P;P<P=PLPNM9VPJPFPKP1P;P<P=PLPNM9cPJPFPKP1PNP=Edn01100000;0000000000000000000000WFb7b8o"). Qed.
End XAll.

Section Startup.
  (* [comment removed for export] *)
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable hw : word.           (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  (* [comment removed for export] *)
  Variables nof sigm : word.   (* [comment removed for export] *)
  Variable abt : bool.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  #[local] Notation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Notation E0a := (AsanInit.E0 APH sp rdraw brk0 argv envp uid hw).
  (* [comment removed for export] *)
  Variable LIM : Z.
  Hypothesis HLIM : source_alloc_limit <= LIM.

  (* [comment removed for export] *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* [comment removed for export] *)
  Variable HS_asan : nat -> option acs.     (* [comment removed for export] *)
  Variable startup_plan : plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert :
    check ASEGS IT0 BOTH NX0 LIM (XNS ASEGS BOTH NX0 LIM) XE0 XB0 HS_asan KC0 BFUEL FUEL None both_init startup_plan = COk startup_shape.

  (* [comment removed for export] *)
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Hypothesis HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs'.
  Hypothesis HOLES_nil : forall h E fs', HOLES h E fs' [].
  Hypothesis HOLES_sound : holes_stmt ASEGS BOTH LIM HS_asan SINV argH HOLES fs.

  (* [comment removed for export] *)
  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.
  Let AH2 := argH0_high2 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit.
  Let AA := argH0_agree APH sp rdraw argv envp uid hw.
  Let SF := SINV0_frame APH sp rdraw brk0 argv envp uid hw.
  Let SA := SINV0_agree APH sp rdraw brk0 argv envp uid hw.

  Theorem asan_startup :
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH sp brk0 mbase rdraw LIM
                                 (AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd))
              (sd HOLES t_nil E0a fs startup_shape).
Proof.
    pose proof asan_img_facts as IMG.
    rewrite (init_cfg_eq ASEGS BOTH APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd LIM AsanUbsan.M.init_pc eq_refl).
    pose proof (init_cs_ok ASEGS BOTH APH sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net IMG Hsp Hbrk Hva Hve Hfit Huid Hhw nof sigm abt urnd LIM HLIM) as HC.
    pose proof (check_sound ASEGS IT0 IT0_ok BOTH NX0 (le_n NX0) LIM HS_asan (XNS ASEGS BOTH NX0 LIM) XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil fs KC0
              (AsanNodesMmB.node_sys_sound ASEGS BOTH NX0 LIM SINV argH fs asan_res_len asan_hull_ok asan_shadow_ok AH2 AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS BOTH NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_hull_ok asan_shadow_ok AH AH2 SF)
              (node_mmap2_sound_OBL ASEGS BOTH NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mmapin_sound_OBL ASEGS BOTH NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (node_mprotect2_sound_OBL ASEGS BOTH NX0 LIM SINV argH fs asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok asan_hull_cov AH AH2 AA SF SA)
              (AsanNodesMmB.node_exit_sound ASEGS BOTH LIM SINV argH fs)
              (asan_node_x_sound_all sp rdraw brk0 argv envp fs Hsp Hva Hve uid hw Hfit SINV (fun E M H => H) SF NX0 (le_n NX0) SA LIM)
              (node_join_sound ASEGS BOTH NX0 LIM SINV argH fs)
              (XNS_sound ASEGS BOTH NX0 LIM SINV argH fs AA SA asan_in_hull asan_hull_ok asan_shadow_ok AH AH2) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None startup_plan both_init startup_shape startup_cert
              _ _ _ _ t_nil HC I eq_refl) as R.
    exact R.
  Qed.
End Startup.
