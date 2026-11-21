(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch's channel reader, the run's segment list (run_segments), the revision's auxiliary vector (auxv_keys), the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame StepTac StartupTac ArgvEnv RefLayout
  Spec SReach RefStartupDefs RefStartup RefStartupFacts RefMainEntry LibDiagKn LibDiagKnMain LibTail
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapCeil HeapSecret
  MainDefs MainArith MainMem MainLoop MainTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells CellsX Arr Step Frame MState SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog AllocTop MmNodes KLink KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface RHeapX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommute VdsoCommuteSys.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common Require VdsoBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase RomStable.
Ltac2 kr_t_RefTop () := KReplay.lz_vm "#%LJC46Stdlib5Lists4!s+#8nil_consC47Corelib4Init5Logic8eq_ind_r!sa+9micromega5Tauto5eKindK!sE;8GFormula04K!t/+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!u=19Datatypes4list00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib:HeapSecret<bytes_le_valC13~~~C4ELinuxProcessSemantics?!s<26BvBase=!sh+to_ZK!tvA1K!wU72eq01C!u{@;bv_unsigned!vk>Z02C5!wz&6ZArith6BinInt1Z3mul!sC=add!sC<6shift!sc>lor!u5AD!u5-_in_range!sYA:bv_modulus!tG<2ltI!vo73and!y&]B!y&/!ty&!y0&!xK:6length!v_=of_nat!v_=pow!sC34Znat5Nat2Z9is_nonneg!sh<>pow_po!sND:!sN#!sJ%!~;66VarMap1t!}J#!sD>0!sD6=RingM!s4'7!~~'0!t567Env!sT#5PExpr!{{#!sIC2!sIE5K!tbL1!#5M;8B!sJ&!sH6:Z!sp+=Z!sT$CheckerI!~2;0C!vc<4find!t3AC!t30_sou!#777!w\,1!sD@3!vaE3!#4l;6op!}K#!wN8!#8`23!}-P9Main!zb$@lor_disjoint_add!}'8!v|%6!#:_$!{M<8!sr#comm!sH<?!#5&$_mul_pow2!#7_A2!~Z<8!sF#!t[@2le!vUF5!sJF8I!#8I>0!#8g?1!#<1<unit!}_8!tN%4kind!#:Y3!sf31!#>GF3!|:84True!#3[7!{u-;!vt%!yf$!t{8!~K13Op2!uj?bool!vP/!sF81!t5I3!sMI5!t<<3na!yy$!#;V>7Z_to_bv!#@,J>Riscv!sE+@word!sh#le_!#:~#!wP3Peano2le!#4d7;ZifyClasses;rew_iff_rev!~IP8SymDriveG!tZ3_of_lez!~O%c!szO6RefTop?!#=I/eq!#3A&!u?@5mkrelI!w[@0!#=,=6inj_!~:#!sg?1!vAQPropExec9u64!#?a/!slO?RefStartupFact!#@,#_av!sp%!}]G!|F=!#8W&!#B;P>!t_,Defs6envp_w!uPV!so3auxv!soX3Amb7a_hwcap!tVe4pn!uEg:progname!ssX7Cat!yQ#6w!{s$!t]e8canary!t[X!{/+3rdn!z73!yj:!|9Q7Seq!t/#>rdn_!ui%_hit!#>s=8!#4c$fl!~vB3inj!#AcD7C8!t|N=Sym!t|#2Sound4SX2S7u_smal!#Q+%!#Ds8or!#75C8or_morph!sNB9and!sO&!ylWD!#LQ$_N!#7^-!y/V:!yw&Tac@!x$-out_Z!~ofD_main!soe3rbn!#9;Japp!sKB6!sK$2!sLCeq_iff!#D6E6I!#>CI<MemImageType7Segment!yi88!tW#Inst7Inj_Z_Z!}CX?!}C18!va&!|8O3Lib5Cells8c!s+#_wf!sl`;!sl%!zn/!soY:!so%siz!#Ue'!#BhW8store_ok!tVZB!uG-_!#Vw%!w,fat!slZ3Mem5wr!sga8!uE%!sj+!#BT<7inj!|5#!#8177iff_sym!|xB7!#FA%!{JQMainMem<!{J#!t}1!#`d7!#\s#1!v+X2wa!yy`5wview!v@83not!#KuC5Psatz!#UD7!sO86!sO6!#Ny:2!#3_Q!|;#Ok<!|C'_!#;x'!x'X5wa!#J='I!|>Y4!|>#00!tS5!sc96images5Plain1M?loaded_s!#72$!#4AWRef5RSegs5rsegs!zB'!wIL1!#30Y7!up#!#76b5c!#6@,!siY6c!#7td=c!#6?5!#O0;!#=y-!#pt,9app_nil_r!#4_'5!w-$8!#ST#Nat3!s&#!#jz-!sF67add_0_r!#RWWrw_!#7f$of_!#H9:!#Y\-1C!#UN8t!s>2!u/$mul!#4nTArr4u64s!vr8!v-+!#5mV3le8!#8n8!#_R'7mul!vj#!sG=!w3&!|=N!#cWP7LibTail9rdn_!y6#Z!v#3!yW%7!s+#Def3n!#mO,!yT7!#qm5!#;U2!sIF!#r>5!sI-8!sI#succ!#X=Ct!{n72In!#L|b9kentry_ok!#7C%!vM:6Fora!#6~#!tV6=!sC%_f!s,$!#;F75proj1!#8IO8!t|'3SX26!tv%!#8N6!soD<RefMainE!sh#7kn!#Kr,K!t_d4!soc4e!#px#!t^k5!sok6!#5&2!#iS53!t5]5saddr01!t}k7!wNi!t^l8!#8a=2or01!#9mV=!z{&_!t2$!{q&!#7yR2Nd:and_elimF3!ufk1!ufB!$%W=sub!#[>D4!#X=P!#VU+C!vO,_rdn_dat!#I\Q5State>stack_max!#QB$!vPO4Spec8AllocTopB!sp1!$/%,!#`yOHeapCeil;hceil!#i+[!sn+5!sn$!shV!$'J,=hs!s-$!t\\!sr-7!sr&!t`c!#d}%!t`h!sr%!sla>!vA&of_draw!}|V!ye$4Prog9reservedZ!sm`7ps_ini!#VHWRef=RMa!{B#_iface5RHEAP!sqZ;!sq&Tree8r!#m~#!#@%&!srT6R!w;#X7eh_imgR!w|V!#>x0!t\#p_u!snc5!sn$!slV9RefLayout8!v7%ff!tZc3rn!$'v&!#7E:6!$7t#oK!#9]R!#Td-!#A[V!sj3!#AX%!#;}V>!#hm$_threads!so]5rdn_D!sf]8!#PE%!#;s%!$#`@9bv_eq_dec!sN';!$-r#basic!$/F$!s7%!sK&3!sK%!#r5%=!s,%!sC24base:decide_rel!#OvZ!x?g!u{+!#K89repeat!t1`5!|-c<!yP&!}i-!#V,W!z?'!#i?/!spW@!sp-alig!#q&V!$$62!tl'page!#[k,!syO!#q}1<!#<b%!#t\Z!tp3!wM'guard!svf>!tn/!#|WW=LibDiagKn!yB#B!#E:-o_non!vcW!#d[#!#\K#!si%_mem_in!$+o%!}aX7!si1!#H449SatDivModCZ_mod!$E;%!s,&!z`W9!u1$hig!#p,Z6M!#H>#C!$67%_!$KJ,!sxWRef>!#@-/P@!#@/#!#A##_p!se#!s}V5Agent9!s~%Rep2wz!tkZ!#A$-:!#A$$lis!$&/'!#ygVph_add!#_s<4of_N!t%X6ph!{M#!sb\num!{yP3Amb5a_ui!~TW!#Af+:!$3w$ord!#dM3!#aL1map!t2Z=!t2,!$:h+!#<e%7tac!v>#<f_equal_help!#:4]!t9+!#ua'!#VLW!#vL&_!#g^,!#3lSArr;!sf#!#lA0!t]O!$3{'8wrap_mem!#6;VArgvEnv!$3^$mem_!#Sl#!sp^4w!tX,!{VJ3RunA!#8U$!#U:$!#t3#!sdK;S!sZ#!yd%<!sf%to!v,$!sgV=a!#T3#dom_ptr!shWAbuild!u?&!#=`$!slV9ed!tV&!sdW?!u<,!tP&!}n95skipn!#Dy;firstn!#py7i!s=8sub!t}WF!$6l%!u+4!#jR4<!sQ&!u/&!#js5!sG&!u2%!#DZWle8!$--'!$dW-!#`156eq!$'G$!#l&:2!#5mY9rnd_fact!#3gZ!#c5/!#IGV!#aB,D!#aB1abov!#C0%!#b`=3P!$PbG!$&s%4!$Qs<prod!$Qs>!sF$!#~dT4TacX!#?g'K!#qxA1!sGC2!#:7\5!x[#u!xWZ4Ste!#S$'!#JTV9StreamSim7wseg!#\#+!#8LO!$-x%=!$-x'!sr#!#=e09!#SG#able;bool_!#SV$!#LPgmissb!u,V!sv3!{P3!#:#$!u<:E!u<-_eq_true_!zFU6!#T$#X<!$%R'app!~S];ex_introF10!#4g7!$+V,fst!sC=snd!#HcS:R!#IP':RAUXV_CELL!uCV!#JF$<!st%Blocks5b!s,#!xR5!sk9!$4615phdrs!#?|P!#:@-7AT_PHDR!sbW8!sb$ENT!sc]NUM!sc[HWCAP!#?hW!tH#AGESZ!sdW6AT_UID!w2[E!sbZ!u'#SECURE!sd[RANDOM!u-[NULL!sbK!#uv$<sp_window_lo!sa\hi!saK3Run8valid_sp!s[O9!s[%brk!ttQ7in_argv!s\Uenv!tpP@!#Ja-fits!scO:!uU%!txO!s]-!tyO!uW%5in_f!tpL2Fs!w{&fs!#;#O!#t[$spec!#5S@5!$Gy#7Prelude5bv!#U$R3Amb6amb_!#[^&I!#ECY:!#<q+!$3}'!#l_?5!#l_#K!%/|C!$hjY7seg_ro!#R1V!$Ft&_!#ye&!y9Q:!#_Q#model!s_Q8with_tidK!s]P9!s7#Input01!t?Q;fs_seed_tm!yLU<mk!tG+C!w+'!#JS3!$`k/not!$`kV!#gO%9ref_usag!#h<^=!ze$realize!$LFZ<!$$m#R!#e7$8hs_!#~B-!zlP!td#!$aI#!yE$0!t^g7hs_KREL!srg;hs_!$#}1!uUX?target_run_stm!$-cV!~7+6fp_csr!uUWLib2FP4frm!w0&!#u4W!#K2,he!$qO'!}/Qi!#Kj%!#9BM!s`%6in!}dT!#7L,;!|R#s!$89%!wK^4mks!$\E'!#6YL6config01!#9\O8ShapeAlg8!}n'!#9X&!$hTE7!uWY3fx!$GcV4Scfg=hunspell_scf!#SS%!$j&J!#FV/!#Vd#Draw00I!#8aZ0!%0\=N00!#@XM2Fs!tTQ;!tP$!#WM$!u8S8NetQue!%0@$!|/PVaSiz!s]#!#:oR!s&#!yo'!$u?75False00!#6RSB!#w8/!#5X#!#Ru-".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib4Init5Logiche2eq37Corelib7Numbers7BinNumsj74Nposj71Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaselbdbytes_le_to_Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~pacbytes_le_val35stdpp9bitvectorbdefinitionsu62bv06length03nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh5h0word_to_le_bytesu67Z_to_bv06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hn3bcells_byteshn3acells_size69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hscfloaded_segments46Stdlib6ZArith6BinInt1Zih52le04Some04bool04truehh58store_okhn34cellhn38cells_wf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~im58rw_cells69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~iqc3rdn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~iue5rsegsih53addih56of_natih53powhn35csize04cons03nilhn36cbyteshn37cell_wfih53mul37Corelib4Init3Natjnb3mul37Corelib4Init5Peanojp42lt37Corelib5Lists7ListDefjqe3nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jsc4u64sih52lt04Nonehe3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~ki05block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref6RHeapX~~~~~~kme7eh_imgR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~kr68rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefdRMalloc_iface~~~~~~lg45RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ll17ps_initll19reservedZu6bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem5Statelr37in_argvlr37in_envplr35in_fs3h5LinuxProcessSemanticsfLinuxProcessSem2Fsmg08valid_fs3h5LinuxProcessSemanticsfLinuxProcessSem3Runmj7h0entry_stack_fitsmj7binit_configmj7avalid_argvmj79valid_brkmj7avalid_envpmj78valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutmrc9EntryDrawlr39ProcInputlr3estack_max_size69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~nhc5hceilpa7hcanarypa7hsecretpaesecret_of_draw69OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs~~~~~~no58canary_w69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~nt2dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~oha8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~om14spechsc7init_pchsc5phdrsih53sub3h5LinuxProcessSemantics5Riscv7Preludeorb5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~ouaamain_entry79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~pj53hsr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~pnf3hmfpj5cheap_sr_hyps69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs~~~~~~pt8aheap_extrapt8bheap_extraM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~qj03mempj58hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~qo65blockll16PStatepj5bhs_rauxv_okmj7h1segments_reservedlr3ainit_modellr38with_tidpj57hs_KRELpt8ftarget_run_stmtiqc3fx0" s.   (* [comment removed for export] *)
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
Lemma bytes_le_val_eq : ltac2:(zQ "70!h8!j2!l0!l7!oa!t7!hg3>2bs@1$0@1$6@1$2#8@3$1$3@1$5^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefTop ()) ["FPX1"] "##;{h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hah76__sat0h8!s/%1h94cstrh:2bsh;4__p1h<4__x2h=1Hh>2Hbh?2Hvh@2IHhA1bp;1p;2p;3p;4p;6p;5p;7p;8p10000p4p710g000MR!s3&p8g000kR1!s5$1g001JR2p4p73101!sD$1nj15Tg002Sj1iTg0031j1X!s/$Tj1ETg0044j13Tg005?j1?Tg006<j1L!s/$\j2JTg0076j29!s/$`j1@Tg008>j20!s/$[j28Tg0098j2Q!s/$Xj2:Tg00:5j2c!s/$hj1[Tg00;Qj24!s/$mj2<Tg00<Hj1YTg00=Yj26Tg00>9j17!s/$Yj2;Tg00?6j1K!s/$[j2ITg00@Cj3H!s/$gj2GTg00AEj1W!s/$cj1VTg00BNj2ATg00C1j2F!s/$Tj3BTg00D7j4=!s/$bj2TTg00EDj2STg00F0j3D!s/$Jj3R!s/$ij4UTg00G[j1hTg00H9j4g!s/$Wj3PTg00I:j1f!s/$\j6bTg00J@j4^TP0j6CTg00KNj6N!s/$jj2]Tg00LLj3\Tg00M5j3_!s/$Uj5`Tg00N7j2aTP2j7Z!s5$Sj7dTg00O7j8e!s/$[R2f1R0f0R33Dp=2g00P9R4/a3p=1P0P1g00PWR5P5g00Q7R6P3g00QWFZp=>f2R7P1P5P5P6P0P3Fdp=Of3R8!s;+7P0P3Gep=Mg00R7R9#5R:#5#5R;#iR<#XR=#ER>P=%33%?3'2R?X:>%L=#?,J2P2%3019<8R@%5;#5!s$&@RA%37RB'0'8%@;R;,Q3,:@'2X521c<719<7R@#1%[<,4@'<%Y7%1B%@:R@16=7#7,0;';,4B'<P2%38RB1;@;'0f5RC,9<RDf4RE#3RF,0ARG'8RH1:D3!t,$P210BARI19<ERJ':12H3X5216=8RH#K%7H#116=ERE#7RH,0;,I@144@RK16=C!tH$RL#1f6RM,6=!s6%N,;@,44[[%1@ROg00R\RPf7RQ!sH+R=H@0UW61;@RRR#1\P^6Og00S8RS#LRT%ESRS1G20RU%W2RV%V2RWP21A2ARX1F29R95B2g00SdRYAB29XC='>1TW6RZP3P7g00TKR[g00TkR\'J1S37=D[\dAR240CUR\b2b3b4X0210A3103A'2^02P3%3QO1b1b7b8b910AB/2IP2PG19<MRQ%3C,0A'8R[1:3Q!v_'8GD12[3X52%KERE%1HRH1I@LRL%1N144R[\KRKf8RR!vA,=H@0VPX6OR[1;@NRN!u{&ROPTPSP21G27P0%h2RPCgPVP21F2:9B2XR:9P29PYAP2:9C=,>WPZP!uE,X<210A0R:,8318:3!uM$^<!uP$RRRf9,9<R<O2!uY+:GDPDPFPEPHPLPKP[P!tP%UPVP!w9%4R4g00UKRDP!t?%RGP2P9g00V2PX!s8$5OWRX%f5R9PXCM!t_0%13RX143A'<%10R:140A'<[!w3$P<PM!tY,!tQ/p-0R!tV/W!}7+8Eb9OWGP9PG!t82W;1<X0P:[^02^;OP314RNPRPCO3!t1'C^EC10FAP3ENb=1:JI1]JIEC1QB;!t<$PPVP2P4PD1A2;!v|2%1;P3b19\B;ECb?b>%?0P3ENA_=70R7#3%?7'2eX@?X:>XA=P3D`W:o"). Qed.

Lemma le8_bytes_le_val : ltac2:(zQ "90!l0!hg3!h8!j2!hg8!hh0!hkc!t7!hm1>2bs@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N8@3$3@1$2@1$1@1$0#8@2$6N8@2$8@1$0#k0@1$7^2^2").
Proof.
ltac2:(KReplay.run1 (kr_t_RefTop ()) ["FPX1"] "h02Hlh17__arithh24__ffh38__varmaph45__with52bsh61zp;1p;2p;3p;4p;7p;6p;<g001nj11Tg002Sj13Tg0031j1=Tg003Tj14Tg00=Yj2OTg00VYj10Tg00F0j32Tg005?j1<Tg00W8j2;Tg00W^j2:Tg00XfR0j26Tg007`j18Tg00N7R1j29Tg006\j25Tg006<j1MTg00G[j1LTg00AEj1KTg00Acj1?Tg00BNj2>Tg00D7j4@Tg001Jj7ATg00Dbj2BTg00EDj2CTg00FJj3DTg00Fij4ETg00Y@j4FTg00Ykj4GTg0044j1HTg00[?j1ITg000Mj6JTg00\Il<7Tg00\nR2g00O[R3P0g00>9P1g00]Mf5f4f3f2R1f1R0f0R4M<7p=Ng00R7#1#1#1R5#3#=R6#4R71O64g00]o#0#0#0#0#0#0#0#0R6522P3%<0%15#1#1#3/;4,:6=271X63P6P0P41666%85R5/95R7P6P51535R2P6P5P2ENg00S8R2#M%42%L3%K3%?3R2g000kg00PWR6P6g00Q7R6P31>35R5g00UKP5C@g00QWFA1B26P4P1g00TKR6g00TkR2'51C41=262dg00P9=D30CEb2b3b4P7P4b1CFCG%H0%I0EJW0W5o"). Qed.
End FPX1.

Section Top.
  #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

  (* LPS 727298f3 port: the section below is written out.  The recorded proofs read the old
     [main_entry] (the pre-revision exploded stack arguments) and the old ten-pair auxv block;
     at the revision [main_entry] is a record over the run's whole input (RefStartup.v) and
     [rauxv_ok] claims [auxv_keys] (Ref/RMallocTree.v).  Shape and tactic text:
     boost-beast/http_request's lib/RefTop.v Section AtMain (OSSV-652 tree), over this binary's
     own addresses, which are read from this tree: the libc words at 0x12b948 / 0x12b950
     (Ref/RMalloc_ifaceP.v [RHEAP_init_proof]), the image range [0x12bac0, 0x12d000) that no
     launch writes (RefMainEntry.v [kn_image]), the canary word 0x12b7f8 and its GOT slot
     0xf8770 ([RHEAP_init_proof]), the entry 0x47284 (RefStartup.v [ref_startup]). *)
  Section AtMain.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables a0s path : list byte.
    Variable envv : list (list byte).
    Variable rdraw : EntryDraw.
    Variable tid : word.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Hypothesis Hva : valid_argv [a0s; path].
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
    Variables (mbase : word) (fs0 : Fs) (stdin0 : InputStream).
    Let inp : ProcInput := mkProcInputC [a0s; path] envv fs0 stdin0.
    Let entryw : word := (0x47284 : word).
    Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
    Variable brk : word.
    Hypothesis Hvl : valid_launch inp.
    Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
    Hypothesis HCE : hceil = bv_unsigned sp0 - stack_max_size.
    Hypothesis HSE : hsecret = secret_of_draw rdraw /\ hcanary = bv_unsigned (canary_w rdraw).
    (* LPS 727298f3: the instance's CONFIG_RSEQ flag is the run's ([kb_rseq] of the input's kernel);
       [rauxv_ok] ties the auxv tail to it. *)
    Hypothesis HRS : hrseq = kb_rseq (in_kernel inp).

    Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
    Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).

    (* The section premises of RefMainEntry's / RefLayout's lemmas, discharged by type. *)
    Ltac sideT :=
      first [ exact ME | exact Hva | exact Hve | exact Hvsp | exact Htid | exact Hvl | exact Hlau
            | reflexivity | exact (proj2 (proj2 Hvsp))
            | (unfold sp_window_lo; pose proof SPlo; lia) | (unfold sp_window_hi; pose proof SPhi; lia)
            | (pose proof SPlo; pose proof SPhi; lia) ].
    Ltac fill H :=
      repeat lazymatch type of H with
             | forall _ : word, _ => specialize (H brk)
             | ?P -> _ => let X := fresh "X" in assert (X : P) by sideT; specialize (H X); clear X
             end.

    Lemma D_main_threads : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12b948) 1 = Some [Z_to_bv 8 1].
    Proof.
      intros segs. pose proof (u64_range tid). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
      pose proof (rdn_wbytes_hit segs [Z_to_bv 8 1]) as Hh. cbn [length] in Hh. apply Hh. unorm; lia.
    Qed.
    Lemma D_main_tls_size : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12b960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 224)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.
    Lemma D_main_tls_align : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12b968) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.

    Lemma rw_cells_of_rdn : forall m (A : Z) cs,
      cells_wf cs ->
      rdn RSEGS m (Z_to_bv 64 A) (length (cells_bytes cs)) = Some (cells_bytes cs) ->
      store_ok RSEGS m (Z_to_bv 64 A) (cells_size cs) = true ->
      0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
      rw_cells rsegs m A cs.
    Proof.
      intros m A cs Hwf HD HS HA HAn. pose proof (cells_bytes_length cs Hwf) as HL.
      split; [split; [exact Hwf | apply rdn_bytes_at; [exact HD | lia | rewrite HL; lia]]|].
      split; [lia|]. split; [lia|]. intros i Hi. rewrite wa_eq.
      replace (Z_to_bv 64 (A + i)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) + i)) by (rewrite u_small by lia; reflexivity).
      apply (store_ok_all RSEGS m (cells_size cs) (Z_to_bv 64 A)); [rewrite u_small by lia; lia | exact HS | rewrite !u_small by lia; lia].
    Qed.

    Lemma rw_cell1 : forall m (A : Z) c,
      cell_wf c ->
      rdn RSEGS m (Z_to_bv 64 A) (csize c) = Some (cbytes c) ->
      store_ok RSEGS m (Z_to_bv 64 A) (csize c) = true -> 0 <= A -> A + Z.of_nat (csize c) <= 2 ^ 64 ->
      rw_cells rsegs m A [c].
    Proof.
      intros m A c Hwf HD HS HA HAn. apply rw_cells_of_rdn; cbn [cells_wf cells_bytes cells_size]; rewrite ?app_nil_r, ?Nat.add_0_r;
        [split; [exact Hwf | exact I] | rewrite (cbytes_length c Hwf); exact HD | exact HS | exact HA | exact HAn].
    Qed.
    Ltac rw_split :=
      lazymatch goal with |- rw_cells _ ?m ?A (?c :: ?rest) =>
        lazymatch rest with
        | [] => idtac
        | _ => apply (proj2 (rw_cells_app rsegs m A [c] rest)); cbn [cells_size csize Nat.add]; split; [| rw_split]
        end end.
    Ltac rw_one RD := apply rw_cell1; [cbn; first [reflexivity | exact I] | cbn [csize cbytes]; RD | cbn [csize]; apply store_ok_wseg; vm_compute; reflexivity | lia | cbn; lia].

    (* A word of the image this launch leaves unwritten (RefMainEntry.v [kn_image]'s KImg rows),
       read from the image itself. *)
    Definition img_w8 (a : Z) : word :=
      match rdn RSEGS (fun _ => None) (Z_to_bv 64 a) 8 with
      | Some bs => Z_to_bv 64 (bytes_le_to_Z bs) | None => Z_to_bv 64 0 end.

    Lemma know_main : exists E, know_ok RSEGS E mem0 kn_main.
    Proof.
      eexists.
      eapply main_know_ok with (inp := inp) (mbase := mbase) (entry := entryw) (sp0 := sp0) (rdraw := rdraw)
                               (tid := tid) (regs := regs0) (mem := mem0) (brk := brk); sideT.
    Qed.

    Lemma none_high : forall i, 1227456 <= i < 1232896 -> mem0 (Z_to_bv 64 i) = None.
    Proof.
      intros i Hi. destruct know_main as [E HK].
      pose proof (proj1 (Forall_forall _ _) HK (KImg 1227456 1232896)
                    ltac:(unfold kn_main; apply in_or_app; right; apply in_or_app; right; unfold kn_image; in_solve)) as K.
      cbn [kentry_ok] in K. destruct K as (_ & _ & K). apply K. exact Hi.
    Qed.

    Lemma rdn_D : forall (a : Z) n, 0 <= a -> a + Z.of_nat n <= 0x12d000 ->
      rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main inp sp0 rdraw tid) (Z_to_bv 64 a) n.
    Proof.
      intros a n Ha Hn. pose proof SPlo. apply (main_entry_rdn_data _ _ _ _ _ _ _ _ ME). rewrite u_small by lia. rewrite stack_max_size_val. lia.
    Qed.
    Ltac rd_miss a n := rewrite (main_entry_rdn_image _ _ _ _ _ _ SPlo _ _ ME RSEGS a n) by (vm_compute; reflexivity); vm_refl_bv.
    Ltac rd_any := idtac; lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) ?n = _ => rd_miss a n end.

    (* Word [j] of the auxv for every word of the vector, [j < 2 * auxv_count rseq] (the
       AT_RSEQ pairs and AT_NULL included), from RefLayout's [read_auxv_word]. *)
    Lemma auxv_word_atR : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
      rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)) 8
      = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entryw
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (rnd inp sp0 a0s path envv)
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                      (Z_to_bv 64 0))).
    Proof.
      intros j Hj. pose proof SPlo as HLO. pose proof SPhi as HHI.
      assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
        by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
      assert (AU : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off [a0s; path] envv))%Z
                   /\ (Z.of_nat (auxv_off [a0s; path] envv) + Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) <= 2240000)%Z)
        by (eapply auxvp_u with (inp := inp) (sp0 := sp0); try exact ME; try exact Hlau; try sideT; try exact brk). destruct AU as [Hu Hb].
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entryw sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite u_small by lia; lia).
      replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
        with (bv_add sp0 (nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j)%nat))
        by (change (in_argv inp) with [a0s; path]; change (in_envp inp) with envv; rewrite w_add_nat; f_equal; lia).
      pose proof (read_auxv_word RSEGS Sv48 inp mbase RPH entryw sp0 brk rdraw) as Hr. fill Hr.
      rewrite (Hr j Hj). unfold rnd. rewrite n_to_le_8_spec. reflexivity.
    Qed.

    Lemma main_entry_heap :
      RHEAP (ps_init (reservedZ rsegs)) [] mem0 /\ rauxv_ok mem0 (bv_unsigned sp0) /\ eh_imgR mem0.
    Proof using All.   (* every section premise, so the top passes them in the section's order *)
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb. hsb. destruct HSE as [HS1 HS2].
      assert (AU : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off [a0s; path] envv))%Z
                   /\ (Z.of_nat (auxv_off [a0s; path] envv) + Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) <= 2240000)%Z)
        by (eapply auxvp_u with (inp := inp) (sp0 := sp0); try exact ME; try exact Hlau; try sideT; try exact brk). destruct AU as [AU1 AU2].
      assert (RN : (bv_unsigned sp0 <= bv_unsigned (rnd inp sp0 a0s path envv))%Z
                   /\ (bv_unsigned (rnd inp sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
                   /\ (bv_unsigned (rnd inp sp0 a0s path envv) mod 8 = 0)%Z)
        by (eapply rnd_u with (inp := inp) (sp0 := sp0); try exact ME; try exact Hlau; try sideT; try exact brk). destruct RN as (RN1 & RN2 & RN3).
      assert (EAUX : auxv_w inp sp0 = auxvp inp sp0) by reflexivity.
      assert (LC : rw_cells rsegs mem0 1227080 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_threads).
        - rw_one rd_any.
        - rw_one rd_any.
        - rw_one rd_any.
        - rw_one rd_any. }
      assert (LC2 : rw_cells rsegs mem0 1227088 [C8 (auxv_w inp sp0); C8 (img_w8 1227096); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8);
                                               C8 (img_w8 1227120); C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; eapply D_main_auxvp with (inp := inp) (sp0 := sp0); try exact ME; try exact Hlau; try sideT; try exact brk).
        - rw_one rd_any.
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_size).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_align).
        - rw_one rd_any.
        - rw_one ltac:(rewrite rdn_D by lia; eapply D_main_pagesize; try exact ME; try exact Hlau; try sideT; try exact brk).
        - rw_one rd_any. }
      assert (GOT : rw_cells rsegs mem0 1017712 [C8 (Z_to_bv 64 1226488)]) by (rw_one rd_any).
      assert (CAN : rw_cells rsegs mem0 1226488 [C8 (Z_to_bv 64 hcanary)]).
      { rw_one ltac:(rewrite rdn_D by lia; rewrite HS2, Z_to_bv_bv_unsigned;
                      change (le8 (canary_w rdraw)) with (word_to_le_bytes 8 (canary_w rdraw)); rewrite <- (canary_bytes_w rdraw);
                      eapply D_main_guard; try exact ME; try exact Hlau; try sideT; try exact brk). }
      assert (MI : mem_inv rsegs mem0) by (apply ro_none_mem_inv; intros i Hi; eapply main_entry_ro_none; try exact ME; try exact Hi; try exact Hlau; try sideT; try exact brk).
      destruct (RHEAP_init_proof mem0 (auxv_w inp sp0) (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 64 0)
                  (img_w8 1227096) (Z_to_bv 64 224) (Z_to_bv 64 8) (img_w8 1227120) (repeat (Z_to_bv 8 0) 48) eq_refl
                  ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply none_high; lia)
                  LC LC2 GOT CAN ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply none_high; lia) MI) as [RH AUXC].
      split; [exact RH|]. split.
      2:{ (* the eighteen image words the exception tables read, and the replaced-malloc flag:
             all in ranges no launch writes, read from the image *)
          unfold eh_imgR, EH_IMG_WORDS18. split.
          - repeat (apply Forall_cons; [unfold img_word; cbn [fst snd]; unfold wz; rw_one rd_any |]). apply Forall_nil.
          - unfold RMALLOC_REPLACEDX, wz. rw_one rd_any. }
      unfold rauxv_ok.
      set (rndw := rnd inp sp0 a0s path envv) in *. set (auxw := auxvp inp sp0) in *.
      (* [rauxv_ok] claims the key words of the launch's vector, the value words below AUX_CNT
         ([auxv_keys]: [auxv_vals]) and the CONFIG_RSEQ tail tied to [hrseq] ([auxv_tie]); key k
         is word 2k of [auxv_words], at byte 16k, its value word 2k+1.  The AT_RSEQ pairs and AT_NULL
         are read for the run's own [kb_rseq].  [x16 x6 x11 x12 x23] are AT_HWCAP's, AT_PAGESZ's,
         AT_UID's, AT_EUID's and AT_SECURE's values; the three phdr ones are fixed. *)
      exists (bv_unsigned auxw), 65600, 56, 10, (bv_unsigned (in_hwcap inp)), 4096,
        (bv_unsigned (in_uid inp)), (bv_unsigned (in_uid inp)), 0, (bv_unsigned rndw).
      pose proof (u64_range auxw). pose proof (u64_range rndw).
      pose proof (u64_range (in_hwcap inp)). pose proof (u64_range (in_uid inp)).
      assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
        by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
      assert (KEY : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
                bytes_at RSEGS mem0 (bv_unsigned auxw + 8 * Z.of_nat j)
                  (le8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entryw
                                 (in_uid inp) (in_gid inp) (in_hwcap inp) rndw
                                 (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                            (Z_to_bv 64 0)))).
      { intros j Hj. apply rdn_bytes_at; [| lia | rewrite length_le8; lia].
        rewrite length_le8. subst auxw rndw. rewrite (auxv_word_atR j Hj). reflexivity. }
      assert (Hrs : la_rseq (launch_auxv inp sp0 mbase) = kb_rseq (in_kernel inp)) by reflexivity.
      repeat match goal with |- _ /\ _ => split end; try (rewrite HCE, stack_max_size_val; lia); try lia.
      - unfold wz. rewrite Z_to_bv_bv_unsigned. rewrite EAUX in AUXC. exact AUXC.
      - unfold auxv_keys, auxv_vals, auxv_tie. rewrite HRS.
        destruct (kb_rseq (in_kernel inp)) eqn:Erseq; try rewrite Erseq in Hrs;
        repeat match goal with |- _ /\ _ => split end;
        try (intros HR; try discriminate HR;
             repeat match goal with |- _ /\ _ => split end);
          try (first [ lazymatch type of Erseq with
                       | _ = true => left; repeat match goal with |- _ /\ _ => split end
                       | _ = false => right
                       end
                     | idtac ];
               match goal with
               | |- exists v, bytes_at _ _ (_ + ?off) _ =>
                   let j := constr:((Z.to_nat off / 8)%nat) in
                   specialize (KEY j ltac:(try rewrite Erseq; cbv; lia)) as K; rewrite auxv_words_eq in K;
                   unfold auxv_entries in K; rewrite Hrs in K;
                   cbn [nth flat_map app fst snd] in K;
                   lazymatch type of K with bytes_at _ _ _ (le8 ?w) =>
                     exists (bv_unsigned w); unfold wz; rewrite Z_to_bv_bv_unsigned; exact K end
               | |- bytes_at _ _ (_ + ?off) _ =>
                   let j := constr:((Z.to_nat off / 8)%nat) in
                   specialize (KEY j ltac:(try rewrite Erseq; cbv; lia)) as K; rewrite auxv_words_eq in K;
                   unfold auxv_entries in K; rewrite Hrs in K;
                   cbn [nth flat_map app fst snd] in K;
                   first [ exact K | unfold wz; rewrite Z_to_bv_bv_unsigned; exact K
                         | rewrite <- (Z_to_bv_bv_unsigned rndw) in K; exact K ]
               | |- bytes_at _ _ _ _ =>
                   specialize (KEY 0%nat ltac:(try rewrite Erseq; cbv; lia)) as K; rewrite auxv_words_eq in K;
                   unfold auxv_entries in K; rewrite Hrs in K;
                   cbn [nth flat_map app fst snd] in K;
                   replace (bv_unsigned auxw + 8 * Z.of_nat 0) with (bv_unsigned auxw) in K by lia; exact K
               end).
      - apply rdn_bytes_at; [| lia | replace (length (le8 (wz hsecret))) with 8%nat by reflexivity; lia].
        replace (length (le8 (wz hsecret))) with 8%nat by reflexivity.
        rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
        pose proof (rdn_wmem_stack RSEGS inp mbase RPH entryw sp0 rdraw) as Hw. unfold wmem in Hw. rewrite Hw by (rewrite u_small by lia; lia).
        pose proof (rnd_facts RSEGS Sv48 inp mbase RPH entryw sp0 brk rdraw) as RF. fill RF.
        destruct RF as (_ & _ & _ & _ & RB).
        subst rndw. unfold rnd. rewrite (RB 8%nat 8%nat ltac:(lia)).
        f_equal. unfold le8, wz. rewrite HS1. unfold secret_of_draw, secret_bytes_of_draw.
        symmetry. apply le8_bytes_le_val. rewrite length_firstn, length_skipn, length_at_random_bytes. reflexivity.
    Qed.
  End AtMain.
End Top.

(* LPS 727298f3 port: the top of the reference side, written out.  The run's segment list is
   [run_segments] (the binary's segments and the vDSO's), and [ref_startup] hands off at main
   with the launch's vDSO layer and thread id on the model.  The main phase is proved over the
   binary's own segments without the vDSO layer ([MainDefs.main_realizes_stmt]), so at the
   hand-off the walk is moved, in this order: the vDSO layer is dropped over the binary's
   segments, which carry no vDSO text ([VdsoBridge.realizes_with_vdso_no_text]; [with_tid] and
   [with_vdso] commute, [VdsoCommute.with_tid_with_vdso]); the read-only view is widened to the
   run's ([RomStable.realizes_wrom], [rom_ext_run_segments]); the walk is moved to the run's
   segment list ([RomStable.realizes_run_segments]).  The launch facts [valid_launch],
   [entry_launch_ok_va] and the channel reader are [Run.valid_input]'s and [Run.valid_entry]'s,
   given by the tops. *)
Section TopAbs.
  #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
  Variable HS : hsr.
  Variable HM : OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ.HeapMF_iface.hmf.
  Hypothesis HH : heap_sr_hyps HS.
  Hypothesis HX : heap_extra HS.
  Hypothesis HXM : heap_extraM HM.
  Hypothesis HO : handover HS HM.
  Hypothesis RINIT : forall s m, RHEAP s [] m -> eh_imgR m -> hs_RHEAP HS s [] m.
  Hypothesis AUXINIT : forall m B, rauxv_ok m B -> hs_rauxv_ok HS m B.
  Hypothesis KINIT : forall tid brk mbase sp lim pi,
    valid_brk rsegs brk -> valid_sp sp -> 2 ^ 34 <= lim -> bv_unsigned sp - stack_max_size = hceil ->
    in_channel_reader pi = true ->
    hs_KREL HS (ps_init (reservedZ rsegs)) (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim pi)).
  Hypothesis TR : target_run_stmt HS HM.

  Theorem ref_realizes_spec_at : forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
    hceil = bv_unsigned sp - stack_max_size ->
    hsecret = secret_of_draw rnd /\ hcanary = bv_unsigned (canary_w rnd) ->
    hrseq = kb_rseq (in_kernel inp) ->
    valid_sp sp -> valid_brk RSEGS brk -> 2 ^ 34 <= lim ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
    realizes (run_segments RSEGS inp sp mbase)
      (init_config (run_segments RSEGS inp sp mbase) Plain.M.init_pc RPH sp brk mbase rnd lim inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof using HS HM HH HX HXM HO RINIT AUXINIT KINIT TR.
    intros sp brk mbase rnd lim inp HCE HSE HRS Hsp Hbrk Hlim Hfit Hva Hve Hfs Hvl Hlau Hrdr.
    apply (ref_startup sp brk mbase rnd lim inp); try assumption.
    intros tid regs mem Htid ME.
    (* the walk moved from the run's segments to the binary's, with no vDSO layer *)
    rewrite RomStable.segments_reserved_run_segments.
    rewrite VdsoCommute.with_tid_with_vdso.
    assert (Hvi : vdso_image RSEGS = None) by (vm_compute; reflexivity).
    apply (RomStable.realizes_run_segments RSEGS inp sp mbase _ _ Hvi).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?r ?pc ?m _) ?M) ?T =>
      change (realizes RSEGS (RomBase.cwrom (mkCfg (mkst r pc m (seg_rom RSEGS)) M)
                                (RomStable.seg_rom1 (run_segments RSEGS inp sp mbase))) T) end.
    apply (RomStable.realizes_wrom RSEGS Hvi); [| exact (RomStable.rom_ext_run_segments RSEGS inp sp mbase)].
    lazymatch goal with |- realizes ?s (mkCfg ?ms (with_vdso ?v ?m)) ?T =>
      change (realizes s (VdsoCommuteSys.cfg_with_vdso v (mkCfg ms m)) T) end.
    apply (VdsoBridge.realizes_with_vdso_no_text RSEGS ltac:(vm_compute; reflexivity)).
    change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp lim inp)) with (model0 tid brk mbase sp lim inp).
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 291792) by (apply bv_eq; reflexivity) end.
    (* the input canonicalised over [amb_of inp], as MainTop.v [main_realizes] does *)
    set (AMB := amb_of inp).
    set (canon := @mkProcInputC AMB (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
    assert (ME' : @main_entry AMB canon mbase (Z_to_bv 64 291460) sp rnd tid regs mem)
      by (destruct ME; constructor; assumption).
    assert (Hvl' : valid_launch canon) by exact Hvl.
    assert (Hlau' : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) canon) by exact Hlau.
    assert (Hrdr' : in_channel_reader canon = true) by exact Hrdr.
    assert (HRS' : hrseq = kb_rseq (in_kernel canon)) by exact HRS.
    change (model0 tid brk mbase sp lim inp) with (model0 tid brk mbase sp lim canon).
    clear ME Hvl Hlau Hrdr HRS. subst canon.
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
    set (fs0 := in_fs inp) in *. set (stdin0 := in_stdin inp) in *.
    clearbody AMB argv envp fs0 stdin0. clear inp.
    pose proof (proj1 Hsp) as SPL. unfold sp_window_lo in SPL. pose proof (u64_range sp) as SPR.
    (* the argument cases in [destruct]'s order: none, one, two (the main phase, below), three or more *)
    destruct argv as [|a0s [|path [|x l]]];
      [ eapply ref_usage; try eassumption; try (cbn; lia)
      | eapply ref_usage; try eassumption; try (cbn; lia)
      |
      | eapply ref_usage; try eassumption; try (cbn; lia) ].
    - (* two arguments: the main phase, with the heap at main entry *)
      (* [main_entry_heap] states its entry fact at the section's [entryw], the literal
         [(0x47284 : word)], which is not convertible to [Z_to_bv 64 291460] as a type argument
         (the two well-formedness proofs differ); the record is rebuilt field by field *)
      assert (MEl : @main_entry AMB (mkProcInputC [a0s; path] envp fs0 stdin0) mbase (0x47284 : word)
                      sp rnd tid regs mem)
        by (destruct ME'; constructor; assumption).
      assert (MEH : RHEAP (ps_init (reservedZ rsegs)) [] mem /\ rauxv_ok mem (bv_unsigned sp) /\ eh_imgR mem)
        by exact (@main_entry_heap HCEIL HSEC AMB sp a0s path envp rnd tid regs mem Hva Hve Hsp Htid
                    mbase fs0 stdin0 MEl brk Hvl' Hlau' HCE HSE HRS').
      destruct MEH as (RH & AUX & IMG).
      (* [main_realizes] reads the entry fact over [amb_of] of its input; [main_entry]'s fields do
         not read the ambient record, so the record is rebuilt field by field *)
      assert (ME0 : @main_entry (amb_of (mkProcInputC [a0s; path] envp fs0 stdin0))
                      (mkProcInputC [a0s; path] envp fs0 stdin0) mbase (Z_to_bv 64 291460) sp rnd tid regs mem)
        by (destruct ME'; constructor; assumption).
      eapply main_realizes with (HS := HS) (HM := HM) (ps0 := ps_init (reservedZ rsegs)) (B := bv_unsigned sp);
        first [ exact HH | exact HX | exact HXM | exact HO | exact TR | exact ME0 | eassumption
              | (apply RINIT; [exact RH | exact IMG])
              | (apply AUXINIT; exact AUX)
              | (apply KINIT; [exact Hbrk | exact Hsp | exact Hlim | symmetry; exact HCE | exact Hrdr'])
              | (rewrite HCE; rewrite stack_max_size_val; lia)
              | lia
              | reflexivity ].
  Qed.
End TopAbs.
