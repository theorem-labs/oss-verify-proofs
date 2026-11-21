(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch's channel reader, the run's segment list (run_segments), the revision's auxiliary vector (auxv_keys), the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame StepTac StartupTac ArgvEnv RefLayout Spec SReach LibTail SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefStartupDefs RefStartup RefStartupFacts RefMainEntry LibDiagKn LibDiagKnMain MainDefs MainArith MainMem MainLoop MainTop.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells CellsX Arr Step Frame MState SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog AllocTop MmNodes KLink KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface RHeapX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommute VdsoCommuteSys.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common Require VdsoBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Common.Cfg Require RomBase RomStable.
Ltac2 kr_t_RefTop () := KReplay.lz_vm "#%MYC46Stdlib5Lists4!s+#8nil_consC47Corelib4Init5Logic8eq_ind_r!sa+9micromega5Tauto5eKindK!sE;8GFormula04K!t/+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!u=19Datatypes4list00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib:HeapSecret<bytes_le_valC13~~~C4ELinuxProcessSemantics?!s<26BvBase=!sh+to_ZK!tvA1K!wU72eq01C!u{@;bv_unsigned!vk>Z02C5!wz&6ZArith6BinInt1Z3mul!sC=add!sC<6shift!sc>lor!u5AD!u5-_in_range!sYA:bv_modulus!tG<2ltI!vo73and!y&]B!y&/!ty&!y0&!xK:6length!v_=of_nat!v_=pow!sC34Znat5Nat2Z9is_nonneg!sh<>pow_po!sND:!sN#!sJ%!~;66VarMap1t!}J#!sD>0!sD6=RingM!s4'7!~~'0!t567Env!sT#5PExpr!{{#!sIC2!sIE5K!tbL1!#5M;8B!sJ&!sH6:Z!sp+=Z!sT$CheckerI!~2;0C!vc<4find!t3AC!t30_sou!#777!w\,1!sD@3!vaE3!#4l;6op!}K#!wN8!#8`23C8!}-N1U9Main!zd$@lor_disjoint_add!},8!v~%6!#:a$!{O<8!sr#comm!sH<?!#5+$_mul_pow2!#7aA2!~\<8!sF#!t[@2le!vWF5!sJF8I!#8K>0!#8i?1!#<3<unit!}a8!tN%4kind!#:[3!sf31!#>IF3!|<84True!#3]7!{w-;!vt%!yh$!t{8!~M13Op2!uj?bool!vP/!sF81!t5I3!sMI5!t<<3na!yy$!#;X>7Z_to_bv!#@/J>Riscv!sE+@word!sh#le_!#;$#!wP3Peano2le!#4f7;ZifyClasses;rew_iff_rev!#<SO8SymDriveG!tZ3_of_lez!~O%c!#3GP6RefTop?!#=M/eq!#3C&!uA@5mkrelI!w]@0!#=1=6inj_!~<#!sg?1!vCQPropExec9u64!#?e/!v5Q?RefStartupFact!#@3#_av!sr%!}aG!|J=!#8]&0!taR>!ta,Defs6envp_w!uTX!sq3auxv!sq+!w5O3Amb7a_hwcap!tXg4pn!uIi:progname!uMX7Cat!y[#6w!{}$!t_g8canary!t]X!{;+3rdn!zA3!yt:!|EQ7Seq!t/#>rdn_!uk%_hit!#?%=8!#4q$fl!#3&A3inj!#AsD7!v{P=Sym!t|#2Sound4SX2S7u_smal!#Q<%!#E'8or!#7CC8or_morph!sNB9and!sO&!ynWD!#La$_N!#7l-!y/V:!yw&Tac@!x$-out_Z!~whD_main!sqg3rbn!#9KJapp!sKB6!sK$2!sLCeq_iff!#DHE6I!#>UI<MemImageType7Segment!ym88!tW#Inst7Inj_Z_Z!}GX?!}G18!wQV3Lib5Cells8c!s+#_wf!sl`;!sl%!#5pZ!so,:!so%siz!#Uy'!#BzW8store_ok!tVZB!uG-_!#W3%!w,fat!slZ3Mem5wr!sga8!uE%!sj+!#Bd<7inj!|5#!#8577iff_sym!|xB7!#FS%!#3&Q7MainMem<!{L#!u#1!#`z7!#]1#1!v-X2wa!y{`5wview!vB83not!#L1C5Psatz!#UZ7!sO86!sO6!#O5:2!#3aQ!|=#Ok<!|E'_!#;~'!x,Z5wa!#JQ'I!|BY4!|B#00!#;J4!sc96images5Ubsan1M?loaded_s!#76$!#4EV4RefU5RSegs5rsegs!zE'!wLL1!#35Y7!uq#!#7;b5c!#6E,!siY6c!#7yd=c!#6D5!#OE;!#=~-!#q5,9app_nil_r!#4d'5!w-$8!#Sk#Nat3!s&#!#k;-!sF67add_0_r!#RnYrw_!#7m$of_!#HD:!#Yu-1C!#Ug8t!s>2!u1$mul!#4sTArr4u64s!vt8!v0+!#5rV3le8!#8u8!#_k'7mul!vl#!sG=!w5&!|?N3!#4ePLibTail9rdn_!y8#Z!v#3!yY%7!s+#Def3n!#mj,!yV7!#r05!#;\2!sIF!#rY5!sI-8!sI#succ!#XTCt!{p72In!x?P!#M/59kentry_ok!#7F%!vM:6Fora!#7%#!tV6=!sC%_f!s,$!#;K75proj1!#8LO8!t|'3SX26!tv%!#8Q'!}lQ<RefMainE!sj#7kn!#K},K!tad4!soc4e!#q=#!t^k5!sok6!#5+2!#in53!t5]5saddr01!t}k7!wNi!t^l8!#8c=2or01!#9qX=!z}&_!t4$!{uV3Lib2Nd:and_elimF3!uhk1!uhB!$%v=sub!#[MD4!~UR:!#Vb+C!vQ,_rdn_dat!#IgQ5State>stack_max!#QO$!t_O4Spec8AllocTopB!sp1!$/J,!#a2OHeapCeil;hcei!$&00!snX5!sn$!shV!$'k,=hs!s-$!t\\!sr-7!sr&!t`c!#e6%!t`h!sr%!sla>!vA&of_dra!#iKV!ye$4Prog9reservedZ!sm`7ps_ini!#VUV!#M5#=RMa!{C#_iface5RHEAP!sr[;!sr&Tree8r!#n?#!#@1&!ssU6R!w>#X7eh_imgR!smV!#?%2!t_#p_u!spe5!sp$!yaV9RefLayout8!v<%ff!t\e3rn!$+F&!#7P:6!$8F#oK!#9hR!#Tv-!#AhV!sj3!#Ae%!#<2X>!#i/$_threads!sq_5rdn_D!sh_8!#PZ%!#<+%!$$6@9bv_eq_dec!sN';!$/H#basic!$/t$!s7%!sK&3!sK%!#rU%=!s,%!sC24base:decide_rel!#P3Z!xEg!u{+!#KM9repeat!t1`5!|6e<!yV&!}s-!#VFY!zG'!#i_/!srY@!sr-alig!#qNX!$$h2!tp'page!#\2Y!#rK3<!#<{%!#|+\!tt3!wW'guard!sxh>!tr/!$#[Y=LibDiagKn!yP#B!#EY-o_non!vkY!#e,#!#\r#!sk%_mem_inv!ssV!}s'7!si1!#HW49SatDivModCZ_mod!$E}%!s,&!znY9!u3$hig!#p]Z6M!#Ha#C!$6y%_!$L6,!sxV!#>h#>!#@Q/P@!#@R#!#AK#_p!sf#!s~V5Agent9!s~%Rep2wz!tl[!#AK-:!#AK$lis!$&e'!#zAVph_add!#`F<4of_N!t%X6ph!{S#!sb\num!#AGO3Amb5a_ui!xk'!#B+X:!$4[$ord!#dx3!#aw1map!t2Z=!t2,!$;R+!#<{%7tac!v>#<f_equal_help!#:J_!t;+!#v;'!#VwY!#w$&_!#h5,!#3tSArr;!sf#!#lr0!#QaO!$4]&8wrap_mem!skV7ArgvEnv!$4@$mem_!#T=#!sp^4w!tX,!{ZJ3RunA!#8_$!#Uc$!#te#!sdK;S!sZ#!yh%<!sf%to!v,$!sgV=a!#T\#dom_ptr!shWAbuild!u?&!#=p$!slV9ed!tV&!sdW?!u<,!tP&!}r95skipn!#E;;firstn!#qP7i!s=8sub!t}WF!$7N%!u+4!#k%4<!sQ&!u/&!#kJ5!sG&!u2%!#DpYle8!$-f'!$eK-!#`^56eq!$+#$!#l[:2!#5sY9rnd_fact!#3iZ!#cb/!#IcX!#ao,D!#ao1abov!#C>%!#c7=3P!$QVG!$'S%4!$Rg<prod!$Rg>!sF$!$#AT4TacX!#?p'K!#rSA1!sGC2!#:?^5!x_#u!x[Z4Ste!#SH'!$@rV9StreamSim7wseg!#\T+!#8RO!$/Z%=!$/Z'!sr#!#=o09!#Sg#able;bool_!#Sv$!#Lfimissb!{QX!sx3!{V3!#:1$!u@:E!u@-_eq_true_!zLU6!#TL#X<!$&3'app!~[];ex_introF10!#4o7!$,9,fst!sC=snd!#HrT:R!#I`':RAUXV_CELL!uDV!#JV$<!st%Blocks5b!s,#!z^5!sk9!$4s15phdrs!#@/P!#:K-7AT_PHDR!sbW8!sb$ENT!sc]NUM!sc[HWCAP!#?sW!tH#AGESZ!sdW6AT_UID!w2[E!sbZ!u'#SECURE!sd[RANDOM!u-[NULL!sbK!#vR$<sp_window_lo!sa\hi!saK3Run8valid_sp!s[O9!s[%brk!ttQ7in_argv!s\Uenv!tpP@!#Jl-fits!scO:!uU%!txO!s]-!tyO!uW%5in_f!tpL2Fs!w{&fs!#=3O!#u7$spec!#5S@5!$H`#7Prelude5bv!#U7R3Amb6amb_!#[n&I!#EL[:!#<t+!$4a'!#m-?5!#m-#K!%0{C!$ieY7seg_ro!#R>V!$G[&_!#zC&!y;Q:!#_c#model!s_Q8with_tidK!s]P9!s7#Input01!t?Q;fs_seed_tm!yNU<mk!tG+C!w+'!#J\3!$aZ/not!$aZ%!y}Q!#gf&9ref_usag!#hU`=!zi$realize!$M1[<!$%P#R!#eN$8hs_!#~|Z1U8!tg#!$b=#!yL$0!tah7hs_KREL!ssh;hs_!$$b]!uY-?target_run_stm!$/LV!~B+6fp_csr!t_V!#HG#FP4frm!w4&!#udY!#KB,he!$rQ'!}<Qi!#Kz%!#9QM!s`%6in!}q$!#7[[;!|_#s!$8~%!wO^4mks!$]='!#6hL6config01I!tDPShapeAlg8!}y'!#9g&!$iNE7!uWY3fx0!v?V4Scfg=hunspell_scf!#Si%!$j|J!#Fg/!#Vz#Draw00I!#8pZ0!%1h=N00!#@iM2Fs!tTQ;!tP$!#Wc$!u8S8NetQue!%1L$!|1PVaSiz!s]#!#:~R!s&#!yo'!$v=75False!%$DQ!#6Y#B!#wZ/!#5]#!#S/-".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib4Init5Logiche2eq37Corelib7Numbers7BinNumsj74Nposj71Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaselbdbytes_le_to_Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~pacbytes_le_val35stdpp9bitvectorbdefinitionsu62bv06length03nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh5h0word_to_le_bytesu67Z_to_bv06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hn3bcells_byteshn3acells_size69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~hscfloaded_segments46Stdlib6ZArith6BinInt1Zih52le04Some04bool04truehh58store_okhn34cellhn38cells_wf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~im58rw_cells69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~iqc3rdn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~iue5rsegsih53addih56of_natih53powhn35csize04cons03nilhn36cbyteshn37cell_wfih53mul37Corelib4Init3Natjnc3mul37Corelib4Init5Peanojp52lt37Corelib5Lists7ListDefjqf3nth79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jsd4u64sih52lt04Nonehe3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~ki15block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU6RHeapX~~~~~~kmf7eh_imgR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~kr88rauxv_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUdRMalloc_iface~~~~~~lg75RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ll57ps_initll59reservedZu6bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem5Statelr77in_argvlr77in_envplr75in_fs3h5LinuxProcessSemanticsfLinuxProcessSem2Fsmg48valid_fs3h5LinuxProcessSemanticsfLinuxProcessSem3Runmjbh0entry_stack_fitsmjbbinit_configmjbavalid_argvmjb9valid_brkmjbavalid_envpmjb8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutms09EntryDrawlr79ProcInputlr7estack_max_size69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ni05hceilpa7hcanarypa7hsecretpaesecret_of_draw69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~no9dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~nt18realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~oh84spec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs~~~~~~ol78canary_whsc7init_pchsc5phdrsih53sub3h5LinuxProcessSemantics5Riscv7Preludeos15bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStartup~~~~~~ov0amain_entry79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapSR_iface~~~~~~pjd3hsr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~po83hmfpjdcheap_sr_hyps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U8MainDefs~~~~~~pu3aheap_extrapu3bheap_extraM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~qjd3mempjd8hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~qp35blockll56PStatepjdbhs_rauxv_okmjbh1segments_reservedlr7ainit_modellr78with_tidpjd7hs_KRELiqc3fx0pu3ftarget_run_stmt" s.   (* [comment removed for export] *)
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
Lemma bytes_le_val_eq : ltac2:(zQ "70!h8!j2!l0!l7!oa!t7!hg3>2bs@1$0@1$6@1$2#8@3$1$3@1$5^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefTop ()) ["FPX1"] "##;{h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hah76__sat0h8!s/%1h94cstrh:2bsh;4__p1h<4__x2h=1Hh>2Hbh?2Hvh@2IHhA1bp;1p;2p;3p;4p;6p;5p;7p;8p10000p4p710g000MR!s3&p8g000kR1!s5$1g001JR2p4p73101!sD$1nj15Tg002Sj1iTg0031j1X!s/$Tj1ETg0044j13Tg005?j1?Tg006<j1L!s/$\j2JTg0076j29!s/$`j1@Tg008>j20!s/$[j28Tg0098j2Q!s/$Xj2:Tg00:5j2c!s/$hj1[Tg00;Qj24!s/$mj2<Tg00<Hj1YTg00=Yj26Tg00>9j17!s/$Yj2;Tg00?6j1K!s/$[j2ITg00@Cj3H!s/$gj2GTg00AEj1W!s/$cj1VTg00BNj2ATg00C1j2F!s/$Tj3BTg00D7j4=!s/$bj2TTg00EDj2STg00F0j3D!s/$Jj3R!s/$ij4UTg00G[j1hTg00H9j4g!s/$Wj3PTg00I:j1f!s/$\j6bTg00J@j4^TP0j6CTg00KPj6N!s/$lj2]Tg00LNj3\Tg00M7j3_!s/$Wj5`Tg00N9j2aTP2j7Z!s5$Uj7dTg00O9j8e!s/$]R2f1R0f0R33Dp=2g00P;R4/a3p=1P0P1g00PYR5P5g00Q9R6P3g00QYFZp=>f2R7P1P5P5P6P0P3Fdp=Of3R8!s;+7P0P3Gep=Mg00R9R9#5R:#5#5R;#iR<#XR=#ER>P=%33%?3'2R?X:>%L=#?,J2P2%3019<8R@%5;#5!s$&@RA%37RB'0'8%@;R;,Q3,:@'2X521c<719<7R@#1%[<,4@'<%Y7%1B%@:R@16=7#7,0;';,4B'<P2%38RB1;@;'0f5RC,9<RDf4RE#3RF,0ARG'8RH1:D3!t,$P210BARI19<ERJ':12H3X5216=8RH#K%7H#116=ERE#7RH,0;,I@144@RK16=C!tH$RL#1f6RM,6=!s6%N,;@,44[[%1@ROg00R^RPf7RQ!sH+R=H@0UW61;@RRR#1\P^6Og00S:RS#LRT%ESRS1G20RU%W2RV%V2RWP21A2ARX1F29R95B2g00SfRYAB29XC='>1TW6RZP3P7g00TMR[g00TmR\'J1S37=D[\dAR240CUR\b2b3b4X0210A3103A'2^02P3%3QO1b1b7b8b910AB/2IP2PG19<MRQ%3C,0A'8R[1:3Q!v_'8GD12[3X52%KERE%1HRH1I@LRL%1N144R[\KRKf8RR!vA,=H@0VPX6OR[1;@NRN!u{&ROPTPSP21G27P0%h2RPCgPVP21F2:9B2XR:9P29PYAP2:9C=,>WPZP!uE,X<210A0R:,8318:3!uM$^<!uP$RRRf9,9<R<O2!uY+:GDPDPFPEPHPLPKP[P!tP%UPVP!w9%4R4g00UMRDP!t?%RGP2P9g00V4PX!s8$5OWRX%f5R9PXCM!t_0%13RX143A'<%10R:140A'<[!w3$P<PM!tY,!tQ/p-0R!tV/W!}7+8Eb9OWGP9PG!t82W;1<X0P:[^02^;OP314RNPRPCO3!t1'C^EC10FAP3ENb=1:JI1]JIEC1QB;!t<$PPVP2P4PD1A2;!v|2%1;P3b19\B;ECb?b>%?0P3ENA_=70R7#3%?7'2eX@?X:>XA=P3D`W:o"). Qed.

Lemma le8_bytes_le_val : ltac2:(zQ "90!l0!hg3!h8!j2!hg8!hh0!hkc!t7!hm1>2bs@1$2@1$1@1$0#8>0@3$3$5@2$4@1$1@1$0#8^1N8@3$3@1$2@1$1@1$0#8@2$6N8@2$8@1$0#k0@1$7^2^2").
Proof.
ltac2:(KReplay.run1 (kr_t_RefTop ()) ["FPX1"] "h02Hlh17__arithh24__ffh38__varmaph45__with52bsh61zp;1p;2p;3p;4p;7p;6p;<g001nj11Tg002Sj13Tg0031j1=Tg003Tj14Tg00=Yj2OTg00V[j10Tg00F0j32Tg005?j1<Tg00W:j2;Tg00W`j2:Tg00XhR0j26Tg007`j18Tg00N9R1j29Tg006\j25Tg006<j1MTg00G[j1LTg00AEj1KTg00Acj1?Tg00BNj2>Tg00D7j4@Tg001Jj7ATg00Dbj2BTg00EDj2CTg00FJj3DTg00Fij4ETg00YBj4FTg00Ymj4GTg0044j1HTg00[Aj1ITg000Mj6JTg00\Ml<7Tg00]2R2g00O]R3P0g00>9P1g00]Qf5f4f3f2R1f1R0f0R4M<7p=Ng00R9#1#1#1R5#3#=R6#4R71O64g00^3#0#0#0#0#0#0#0#0R6522P3%<0%15#1#1#3/;4,:6=271X63P6P0P41666%85R5/95R7P6P51535R2P6P5P2ENg00S:R2#M%42%L3%K3%?3R2g000kg00PYR6P6g00Q9R6P31>35R5g00UMP5C@g00QYFA1B26P4P1g00TMR6g00TmR2'51C41=262dg00P;=D30CEb2b3b4P7P4b1CFCG%H0%I0EJW0W5o"). Qed.
End FPX1.

Section Top.
  #[local] Existing Instance OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.fx0.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

  (* LPS 727298f3 port: the section below is written out.  The recorded proofs read the old
     [main_entry] (the pre-revision exploded stack arguments) and the old ten-pair auxv block;
     at the revision [main_entry] is a record over the run's whole input (RefStartup.v) and
     [rauxv_ok] claims [auxv_keys] (RefU/RMallocTree.v).  Shape and tactic text:
     boost-beast/http_request's lib/RefTop.v Section AtMain (OSSV-652 tree), over this binary's
     own addresses, which are read from this tree: the libc words at 0x12ee88 / 0x12ee90
     (RefU/RMalloc_ifaceP.v [RHEAP_init_proof]), the image range [0x12f000, 0x131000) that no
     launch writes (U/RefMainEntry.v [kn_image]), the canary word 0x12ec38 and its GOT slot
     0xfbc78 ([RHEAP_init_proof]), the entry 0x46e98 (U/RefStartup.v [ref_startup]). *)
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
    Let entryw : word := (0x46e98 : word).
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

    Lemma D_main_threads : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12ee88) 1 = Some [Z_to_bv 8 1].
    Proof.
      intros segs. pose proof (u64_range tid). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
      pose proof (rdn_wbytes_hit segs [Z_to_bv 8 1]) as Hh. cbn [length] in Hh. apply Hh. unorm; lia.
    Qed.
    Lemma D_main_tls_size : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12eea0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 224)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.
    Lemma D_main_tls_align : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12eea8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
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

    (* A word of the image this launch leaves unwritten (U/RefMainEntry.v [kn_image]'s KImg rows),
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

    Lemma none_high : forall i, 1241088 <= i < 1249280 -> mem0 (Z_to_bv 64 i) = None.
    Proof.
      intros i Hi. destruct know_main as [E HK].
      pose proof (proj1 (Forall_forall _ _) HK (KImg 1241088 1249280)
                    ltac:(unfold kn_main; apply in_or_app; right; apply in_or_app; right; unfold kn_image; in_solve)) as K.
      cbn [kentry_ok] in K. destruct K as (_ & _ & K). apply K. exact Hi.
    Qed.

    Lemma rdn_D : forall (a : Z) n, 0 <= a -> a + Z.of_nat n <= 0x131000 ->
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
      assert (LC : rw_cells rsegs mem0 1240712 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_threads).
        - rw_one rd_any.
        - rw_one rd_any.
        - rw_one rd_any.
        - rw_one rd_any. }
      assert (LC2 : rw_cells rsegs mem0 1240720 [C8 (auxv_w inp sp0); C8 (img_w8 1240728); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8);
                                               C8 (img_w8 1240752); C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; eapply D_main_auxvp with (inp := inp) (sp0 := sp0); try exact ME; try exact Hlau; try sideT; try exact brk).
        - rw_one rd_any.
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_size).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_align).
        - rw_one rd_any.
        - rw_one ltac:(rewrite rdn_D by lia; eapply D_main_pagesize; try exact ME; try exact Hlau; try sideT; try exact brk).
        - rw_one rd_any. }
      assert (GOT : rw_cells rsegs mem0 1031288 [C8 (Z_to_bv 64 1240120)]) by (rw_one rd_any).
      assert (CAN : rw_cells rsegs mem0 1240120 [C8 (Z_to_bv 64 hcanary)]).
      { rw_one ltac:(rewrite rdn_D by lia; rewrite HS2, Z_to_bv_bv_unsigned;
                      change (le8 (canary_w rdraw)) with (word_to_le_bytes 8 (canary_w rdraw)); rewrite <- (canary_bytes_w rdraw);
                      eapply D_main_guard; try exact ME; try exact Hlau; try sideT; try exact brk). }
      assert (MI : mem_inv rsegs mem0) by (apply ro_none_mem_inv; intros i Hi; eapply main_entry_ro_none; try exact ME; try exact Hi; try exact Hlau; try sideT; try exact brk).
      destruct (RHEAP_init_proof mem0 (auxv_w inp sp0) (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 64 0)
                  (img_w8 1240728) (Z_to_bv 64 224) (Z_to_bv 64 8) (img_w8 1240752) (repeat (Z_to_bv 8 0) 48) eq_refl
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
  Variable HM : OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU.HeapMF_iface.hmf.
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
      (init_config (run_segments RSEGS inp sp mbase) Ubsan.M.init_pc RPH sp brk mbase rnd lim inp)
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
    lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 290788) by (apply bv_eq; reflexivity) end.
    (* the input canonicalised over [amb_of inp], as U/MainTop.v [main_realizes] does *)
    set (AMB := amb_of inp).
    set (canon := @mkProcInputC AMB (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)).
    assert (ME' : @main_entry AMB canon mbase (Z_to_bv 64 290456) sp rnd tid regs mem)
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
         [(0x46e98 : word)], which is not convertible to [Z_to_bv 64 290456] as a type argument
         (the two well-formedness proofs differ); the record is rebuilt field by field *)
      assert (MEl : @main_entry AMB (mkProcInputC [a0s; path] envp fs0 stdin0) mbase (0x46e98 : word)
                      sp rnd tid regs mem)
        by (destruct ME'; constructor; assumption).
      assert (MEH : RHEAP (ps_init (reservedZ rsegs)) [] mem /\ rauxv_ok mem (bv_unsigned sp) /\ eh_imgR mem)
        by exact (@main_entry_heap HCEIL HSEC AMB sp a0s path envp rnd tid regs mem Hva Hve Hsp Htid
                    mbase fs0 stdin0 MEl brk Hvl' Hlau' HCE HSE HRS').
      destruct MEH as (RH & AUX & IMG).
      (* [main_realizes] reads the entry fact over [amb_of] of its input; [main_entry]'s fields do
         not read the ambient record, so the record is rebuilt field by field *)
      assert (ME0 : @main_entry (amb_of (mkProcInputC [a0s; path] envp fs0 stdin0))
                      (mkProcInputC [a0s; path] envp fs0 stdin0) mbase (Z_to_bv 64 290456) sp rnd tid regs mem)
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
