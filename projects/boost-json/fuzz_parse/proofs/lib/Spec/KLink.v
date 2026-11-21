(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch's channel reader. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv AllocTop VmKit MmNodes GapGrid.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec RefNodes HeapCeil.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_KLink () := KReplay.lz_vm "#&gVC47Corelib7Classes9Morphisms6Proper!sI5?Relation!sY'Reflexive!sR-Program6Basics4flip!t;?:forall_def!sM?Krespectful_per_oblig!tZ$_1C89OSSVerify!u2#ofs:boost_json:fuzz_parse3lib4Spec6Malloc4aptrC13~~~I!sjT5STree5stree00!sl%!u8,4Init5Logic8eq_ind_r!sD29Datatypes3fst!u;]o!u;+K!tM72eq01!s@,7Numbers7BinNums8positive02!sK=1Z!sD?!si,1C56Stdlib6ZArith6BinInt1Z3pow!sC<2ltI!v:;:comparison00K!sLG2!vi\=!s+$_ceiling!vr3!um=3C4ELinuxProcessSemantics?!s<22Fs4path!y><trans!stN2F!sTL5State7PipeBuf!s\Q9!v7%top!x2>eI!uL73and00!s]<>pow_pos_nonneg!sN<:!sN#!sJB7!xs%e!y<<4list01I!sFA0K4!t/&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!}m#!sIC2K!t?L1!v6<6opti!|H#!~`>N!t98!t\27!sI65Tauto8G!tU'8C!sJ<B!sJ&!sH6:Z!uG+=Z!sT$CheckerI!#5J:0C!wo<4find!t3AC!t30_sound!uSF4!sJF5!uw<5eKind!z]=uni!z]9!se%4kind!xU>!sf%1I!~YP6VmMaps00!#6TO3Lib6Decode8CEIL_MIN!#;i%!smaAX!#7=B1Z!~@4!y'%4True!}X#!s`>!}v7!y+-;!#3x$!u,$!wO8!}113Op203!sMI5!xe=bool!#;B=!sF%!#<i=op!#7]<3sub!sC<4land!sa=ad!sC>div!sC=mul!sC<6modulo!#84<div_mod!#<273not!s`<=mod!#9b#b!~+#!sMAneg!sM25!wr$8PreO!s/#1Z;!tW#0_r_ext!sL>!st#!sL&!x1<3nat!#7qE5Psatz!sOM7!sOK5!|]@3!#8G=3P!z:#!t6K!#5u6!|m;2!sRN3!#>1A!sr7!#=K+1!sD@3!#7yE7!v@>!#;a%6!sIE5!sIE3!sIE4!~,=ones!sD<9!~K#_!sI$!#GfZ;r!|@#_up_pg!#M#&!#9bN?page_!sk+Z!ymK6!#6aH1!#FsQ!t\$size!}nA1!zgN!#:885False00c!#Q;TKLink<!tx+_eq!#<UU!#P]/PGSZ!sj%!t][7!si#!tX+!sl[>!yc-!uM,!v]76eq_sym!#?@[mmap_len!t1'!|/14Zdiv:Z_mod_mult!~mF3!wDU5Monad1M!x+[!sf%5mbind!sj[7MmNodes;unsigned_wz!#Xl%45stdpp9bitvector;definitions2bv!#DMQ!t=$4KInv2!t1'!#7h<prod!}r#!tQ?;bv_!u+'!tXZ4went!vY[!sh$3elo!yZ'!t{?7Z_to_bv!#[V<snd!tR\hi!wz'!vo@0I!t/Y6pwdisj!#^0+!{t&5Lists4!s+#2In!}^<!#N7#!sB69!#5Y#!sE$!tfY5e!te#!#3+=7f_equalK!sC72or!#MO3!s@,2I!s@;0!x2<8list!uF#!#36E6!tH8!#Kv$1!y<=app!#:pP:iv_overlap!s|<4negb!s}Q;region_free!s~<9andb_pr!#\1=9ltb_spec!#[u<3ltb!{?<7reflect!w\>4!tT#!#M`A2!#:PZ?!u~-_InZ!#3S_4vmwf!#<0`@!t^/!|+,K!~Wa2!#7V7!#`{,1!~r76filter!sA79!sA%_In!thb1!#4A<7ex!s2#!{?R:map_remove!s_;5Riscv7Prelude6bv_eqb!ww[=!u?%_!vJ&!uD&!u$O=maps_subtract!#^Z9x!|/#!~?Piv!sz+!x08in_app_orK!t@;!#=VAD!#=V,_in_range!sYA:b!#U]#ulus!#Vg=in!sC>ax!#W+<ltb_lt!#Mb=f_N!#`W5;Zify!#tl%!#;6#ff!#l[8iff_refl!sjB3inj!sIB9and_morph!sOB7rew!t_%!x19or!x4#!ui<8min!#7E#!#H7TM!y]$<!xP+li!#BH&!t;=ax!t;%!uJA5mk!#;M#!wOA!sK$2!sqErel!#aU=N!#gz78!si#Inst7Inj_Z_Z!#EV[cov!~RW:live_bytes!#:X[!si,_cons!#A}2!#~?:BPreOrder_!#~H6!s[:;r!sR&ity!xn<;le_preo!t'#!#ufM9!#7#$_eqC3!#3C$7tac!sS#<!#D,%_help!#<@[!#8_+_noti!#PA&7!suN7Rel!sx#;!ty&!~c$!#=~`!td-sp!|j,!#@u:6leng!#y{33Nat!#g4#!s=6!#fh>6of_na!#6$34Znat5Nat2Z7inj!#5_;7iff!#Tl#!sf=9i!#xm'!}xA;!#57%_rev!#5;6:!uo%_ap!xp\>!|8-app!#N%A!#[f#!#FL+5!uP$8Peano!vu#!vy:!vY3!sIA8!sI#succ!t5@!#lU5!sj-;!sj%b_max!v8[8sum_g!#Y='!sm`m!smd=!t\'!#4~-!#>H;!#C:^!t~'!t7/!#8PX9bump_meta!}w3!{&%7!s+#Def3map!{E?mapi!uDZ3KLB!#U1'!sjT!#\/&5mminv!|&B!$#[&!#EbQ8m_halted!s]Tvmmap!#;i[7kb_!uL,!sl_!u5#!sla5kb_!#P'&!$1uQvm_!u|cna!tJY;vm_noac!s;#!tN_resv!|v`7ld!skaProg5rba!#eA'!u~Treserved!u~[6kb!$6L#!#6i`!zK#cei!#?e%!#@TO8HeapCeil5!sh-!tW[;!xD&!uI,!vpQ<vm_start_brk!tS[:!tS'!#Ymb9!so'n!#5X75!#=-#2l!#rN]!x##!uf$!vKW6vm!vE_!uT#group!#;2ald!smg8brk!#]q,!vo_meta!t[bld!sl/!{t_distinct!yX'!#>'45NoDup!yZ]!x6#brkreg!x6d!sm/!$>bC1!wj_phase!t~`6!t~%!wha7kb_live!}5W=vm_!#T_d6ltotal!{\ecoun!#?ta6l!skf8!vq$mi!#5%W8!vr$mitk!tLZ!#Fu#!#ge%!#unY4mled!#Ga&!$AYP5Model!#|1[3ww!#n%`7LEN!$AP+!uvZ9brk!}V%!u{'!yf\BUDCAP!xwW5m_fd!$R0Q4m_fs!t5Tti!#KGQ7m_stdin!s\Tcred!tnUnet!#54[vm_only!{1W7FdEntry00!s^Q;InputStream!sbS5C!v@#!s\S8NetQueue!#osSwith!#P[a3!{I#!#6-`RESV!}k,!#TZUGapGrid6GRID_J!sm&6!v$I3Sys2Mm4Mmap:!~W#grantsC5!seM7Syscall5w_is0!#rI@6b!#t-#!#XB'4Bool!s'$<!$#<#f!$+j#r!#Z~;:ltb_ir!#e@#!uXV=!uX#!#vW#next!vB\un!sj#!seWD!#w|/!#us$!soX>!u@$odel!uA$!z;[?!uE,_no!#Q=bB!v}0!sw-!#\o\!$8d'!#x-@ge!sF<7eqb_neq!#lIWD!$E^1_mon!$8$G5!#m&#!$8LAbv_wrap!sLA@!$8r%!$:t+!sU@?!|p%!$;J]!wA'8!~-$!$>8'!y'[A!$-:-intro!#4P\;!#4P$ow_ok!#mX59SatDivModC!$C+$!#n&$!#n1&!u7O3Lib9LiaTuning9zify_done!u2]!#4&#budget!u4#!#i8;leb!{R>eb_le!#;,P>!$ky'_room!~;\!x6/shrink!#C_V>stack_!#~S#iz!uAR:two_pow_64!#S4[!#FX#_!#f~'!#S4Zse!#]:#ph!|+a:l!y,$yte!#Vja8!so$c!$F7a!#Ir#quie!sm&K!sm^!#Ja$2!sok3!sok1!sok4!sok5!wz[6MSafeP4et!#l7'!sj\assn!sjb5m!$1^#!skZ!$Qo$4mg!z;'I9!#7WQ5ITree3Exc3exc!#Qt&K!smb!{$W!sm,5i!%+E#1!v4V!sk-e!$T|+!#U+UProg6P!#6@#!#xad6mmsafe!t[V!uF$!sj$4nod!#V\c8frame_ok!wf[!tY-9!zscsy!#h@\!we#:!#9F%_!#je\!tY'upd!sicret!uD`6ps!#er+K!#3UU!#@A#2ev!|F'!y:[<ev_step_post!{`c!#Ob#resu!#~4&!#D5V!#8E#zeros!tW]=n!uJ$!sp#iff!#3`Y!$cz&dec!sp#0!uI]=!#Y>#!t\#!#QA^Cb!#R0/!#PL,K!#DRO=!#W5%Effect01!#Sd[!#Oa$!$KE#!vzZ5no_cc!z5cA!$0R#_!#]C,!sxcD!$0H&!s{6!#eHS!#dlQ9m_vm_lazy!s^QA!s^$materialized!y,Q7Vm!#;G$1!uYTio!sYQ6m_fsys!s[Tproc!#gESlim!t7Ttime!v\Q!#o?%!vZUv!tlR9vmst!$4G_:KLB!yA#eq'!#:b_5ps_fa!sidso!#:``C!#l2%!}a7!$Gk55proj2!$SS<!$K-&!t][;!v|#re!#}U_!#45&@!#9-/!$zO]!sw+!#=7+_query!sw[!#L>%9!#L>#_!#Cb]!so1!#Bx]!#AI%>brk0_answer!#Fx'!z\Z4ps_m!z[a<!z['!$Qq+!#e^<sub_0_r!t|V!#S5#!uk2!#JT[an!$X$#!#Xv`:event!#E+,!t]\ev_costb!smik!zgi!#Iv]!so&:!so%!%#kY!#N]+5!#Fi#!si&7!t[Pcfg=hunspell_scfg!tW[!#T1#4res!$U;'!#<%O!yA$!#zsR7MemCopy00!ulUE!ul+!#fx$force!#4$b5TWO6!#^0%I!sk[6mst!#W'Z!#G~,7!#Kz%!sla:listNN_eqb!soa=!so,!#:ce?!#:c,grow!tjb!#<M$w!#L<#s!sra8!#Qm#_of!xtV!x+/!ta#ans!#`-'!snc2!snj!#Vjb!#pv+l!$eO8!$cn%and_in!$OX[;!%9\&_ge!u$a8elo_!%4[+!sm]hi!smf@!%db/!vb,!suT!$:i$l!$&;%!wO=3!$hX/!%m@4Diff_impl_subr!$ny&!$_U6!${<%!svB:!%n8+!sM?@!t<-!$xg%!sS=F!sS1!t-GB!sY/p!%qW9!sU,I!$q[&e_!s0,proxy!s\?NR!sR,artial!v@$m!sF&!vd;!{@#!vdBF!tT0per!t[4!%s>1!x0#!sw5>!sw+_Prop?or!$mF#!to,!sW3!$tk2=!sU#!$uC,!uG58!uD#!$g2#!{%Y=l!#\u&s!#Fuc!$&d/!wP#r!|l[!%N`'!|m$!%7Q$!|r&!uy57!%w:$b!sB7>!sB&_!s-%!tX]iv!$UO#oi!#40b:In_!#3=/!so[>went_In!%[?$!ssbA!#8>'!$3N&!svaC!%L}-al!$2D$!#5|6!$tl,or!$<b6:orb_true!#O<Q!#<k,9!%ec#BAN!$A<a>!#j1$!#DG%'!ssaB!#Yb,!#Yi/!sw[9!~$$dea!w/'!#S';add_mo!#>Z[Ab!$57+_fact!u/bD!#k[1!t%#n!yC3!#5x;eq_Tran!%zz$!sVE<eq!%+l>!#8Q+J!#8Q+eq_dom!#:8+!#<G?!#902!sS??eq!#9V:!u5>Symmetric!sUE8s!sR%!#<5?M!%}]#_co_!%L`#v!#?u$!#:C&!y<\KLB_!#9S5!}{U!%75$C!$?I&!$?L-!|?avmwf!$|6,!#Eq_pair!smclo!sm-!}u<4!%&\#!t3T!#\A$!#~@%!$e^]!&,S&!#L?%!#^mfA!#Zf$g!tj#ind!#R>+!%+q<6inj_le!%lYB!%lzC2C5!|#+!%<#%6PosDef3Pos!%3P?7pos!$P6/!sG&:!s,%_dec;Z_lt_le!s2#!$qN16!uu#if7sum!%v/$!$DYBdiv!$DY1!tg<!sQ#!u0#!tgAe_gt!s2#!sn<2gt!%hxH6!#NL[!#?\'!#>a1!#]\N<vm_!sn$bas!$C1Rvm_init_sp!#tYP!&#M&!&<{\>!u%$!#k'c!#^2&is_er!#H=[8A!sk#TopA!#V]+same_s!#D5a?!xO+!|;#!%pu&!st[<wcov_rf!$w%,!#5^Y!$G@#!$v;,!%qqJ!%V'+7Sorting;Permut!#<c#B!s2-_midd!#4O,!$vJ42!sr@A!sr/!sW$!#;,[!vT$!$Uj,!#91]!$|2`!#91&!zk%no_form!~Q'!v&&!#Io+>!#Io'!$T?$!u,UProg9neg!t<%!#:Ba!%B$,!#6~%!u|U!#KZ,6avoi!#Nt&!$SR<!#fm%!t3Z<!#3k$dd!#3i^!#{?'!ss$!$eQ#_co!#Q$'!#6pP?vm_backing_us!$[@^H!sp2_le!${0#!#NUa@!xV-In_l!$#g\!$ih%:gap_!%`^$!sqc!$j[$W!z7a=dec!#;v$n!$[q+!srZ8!sr'!yrc4pgu!%6JX!#^=%tain!%==\BUD_g!u<e=!vu%a!#R'$!stirw!st/!$J^_:!x[Z!sj%6eff!#?I]!$>g'!#Y:$!vH'!$DI'!#pgZ8!#A~&!#qX&!#Z-[!#6&-!$g&/!ubhrw!ub,!#A6[KLB!vX&ew!tk[!#<s%D!sn$fixed!#E\2!$Lz_2!tf[!#?K#4MAPF!sh%I!y#d0!vAb9PROT_NONE!sob7!so$RW!#57V6ENOMEM!vnVProg;MAP_FIXED_!&5<a<ev!z9%cor!%:r\!tb#>!#9w'!z<$!sr`7!$SA%!yIV!sk,9!{l+!yI'".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~0dalloc_ceiling46Stdlib6ZArith6BinInt1Zkd2ltkd3pow3h5LinuxProcessSemanticsfLinuxProcessSem5Staten09alloc_top37Corelib4Init5Logicqa3andkd2len06VmMaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~t28CEIL_MAXt28CEIL_MINqa2eq37Corelib7Numbers7BinNumshia1Zn09page_sizen0fpage_round_up_Z0bround_up_pgt28mmap_lenkd3addkd6modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~hod3elohod4wenthod3ehihia4Npos35stdpp9bitvectorbdefinitionshu72bv37Corelib4Init9Datatypesiga4pairhu7bbv_unsignediga4prod36Stdlib5Lists4Listik12Iniga4listqa2orhod5edisjhod6pwdisjiga4booliga4truen0bregion_freeiga3apphod4vmwfiga4consik16filtern0amap_removeiga3fstiga3sndqa2exn0biv_subtractn0dmaps_subtracthod4wcovn0alive_bytesqa3notiga6lengthiga3nat37Corelib4Init3Natji33subkd3subhod4mlediga6optionhod9ld_brkreghod9brk_phasehod6ld_brk04PGSZkd3mulkd3divik1afold_righthod9ld_groupshod8ld_metas79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink~~~~~~jr1albrk_bytesjr18sum_glenjr18sum_mlenkd6of_natjr18lbrk_cnt37Corelib5Lists7ListDefki93maphod9bump_metan05Modeln08m_vmmaps89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink2HC~~~~~~km73KLBiga4Nonen08m_halted79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~ks15mminvn06vm_brkn08vm_limitn07vm_mapsn0bvm_noaccessn0bvm_reservedn0cvm_start_brkiga4Someqa4Truen07m_credsn05m_fdsn04m_fsn05m_netn07m_stdinn05m_tid3h5LinuxProcessSemanticsfLinuxProcessSem2Fslp42Fsn05Credsn07FdEntryn0bInputStreamn08NetQueuekm77vm_onlyn0bwith_vmmaps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~mg96PStatemg95ps_famg95ps_soiga4unitiga4negbmg9bMAP_FIXED_Zkd3eqbkd4land02evkm78ev_fixed04aptr0cundef_reasonqa5Falseiga5false06is_errjr16BUDCAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7GapGrid~~~~~~mt46GRID_Jkm78RESV_MAXjr16lcountjr16ltotalkm73BUD5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapnk4dbrk_maps_nextiga3nilnk4abrk_unmapsnk4ebrk_model_nextks12wzhu77Z_to_bvnk4bbrk_grow_okhodaevent_postmg94ps_mhod9answer_okkm78ans_contkm78ev_costbkm78ev_costk06mstatemg96ps_brkhod9set_brkphkm79phase_invhod6BPDeadhod9BPQueriedhod9brk_quiet79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~om75mbindt28dec_brk079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~or84NBrkhod9BPUntriedkm7cev_step_postkm78frame_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MSafeP~~~~~~pi55mspec04EBrkks16mmsafeom74mretom74msysom74mupdmg9aset_brk_pst27brk_ansn05eventt27dec_brkt28BrkGrownt27BrkSame79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~pt34respor85nstep69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~qi0dhunspell_scfghod7ld_resvhod7lrangeshoddlbrk_pages_okom71Mom74mgethod6BPLiven0cmkVmMapsFulln0avm_init_spn0cvm_mmap_basehod7LEN_MAXhodaset_groupshod9set_metas0emmap_answer_ok0dis_errno_formmg99neg_errno69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ri35hceilt2cmmap_addr_okn0fvm_backing_usedks1h0mmap_grant_condst28mmap_anshod4MAPFt28dec_mmapt2ddec_mmap_noneor85NMmap05EMmap09PROT_NONE07PROT_RWmg97ev_step" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma alloc_ceiling_lt : ltac2:(zQ "30!je!m5!ma@2$1$0@2$2+2+jf").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##&Qp;2p;1p-1R0p10000p4p710p9P!s6%S!s611?R1!s8,P!s2$2!s3/31!sS-]!sc12D!s6'p1003<p4p70!tF%4@!sA&8!sQ%5F!s6%R1!s8+d!t:&R0p8p1006A!sf%2P1p8P2P0p8g007Ej25Tg007_j14Tg008Dj11!s/$bj10Tg009Gj23!s/$dj22Tg00:@g00:f'5g00;Lg00<YR0#4#1%00#!s$'1'3'2do"). Qed.
(* [comment removed for export] *)
Lemma alloc_top_lt : ltac2:(zQ "90!pe!re!s4!m5!s9!hgf!hha!je!ma>1h$4>0@2$1@2$2$6@1$0^1@2$2@1$0^1$5@2$1@2$1@2$3Z@1$0^2@2$2@1$0^2$7@2$3@1$0^2@2$8+2+if").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##2^h02Hah16__sat1h24__x1h31Hh47__arithh54__ffh6!sK%0h78__varmaph85__with91hp;1p;2p;3p;4p;8p;7p100=>p4p70R0!s3$np4p710R1p8P!s8$5F!s8&0p8p100>L!sU%2P1p8P2P!s=&?:!s=$P0p8g00@0j1<Tg00@hj21Tg00ADj24Tg007_j10Tg008Dj1:!sA$_j2GTg009dj25!s/$Gj2ETg00BGj3D!s/$kj2C!se$Ej2?Tg00CLj1@!s/$lj1UTg00DLj2T!s/$jj1STg00EHj1OTg00F3j27!s/$Vj2FTg00G9j48!tU$bj13!s8$dj1HTg00HFj1I!s/$dj3JTg00IGj8K!s/$kj2BTg00JMj2LTg00K9j3M!s/$Sj3ATg00L2j4P!s/$dj7QTg00MHj7RTf0R0#3!s$%p=2%30#3p=N%00#0p=>!s-$#!s2$=!s2+!s$'p=6f1R2g00MlR1g00NKR3P3g00NkR4P0g00OKFQp=9f2R5P1P3P3P4P2P0FRp=;g00Okg00Pb%<0R6'1g00Qi,16'4g00<YR6#0R7#:R8%27!s/$9'Gg00S0R:/58R;11:91E89R<,5:[R=[11:8R>g00SNR?AD892UW011:<\?^0>P2g00:@1C:8'?P;eO1P=g00SjR=g00THR;#@%U;1T=2%S=%O=R;!u&+=%N6#2#2#2R1#0!s0$0#>#=#6#6#:R>,7=g00U4R?1F=6R6C8,9;P=P6P?%31!sV41,7=!sI$R?5;;%H3P=17=:g00U[R3P!se%=;;?!si$317=8%I75J!s[%5;;GK1B;4P0P5g00VBR;g00VbR4'?1L05=M;4dAA=:2CPb5b7b8W211>01101'415:2112!s0$2<'4[^2=P0f5#<f4O2b4b1b6b1%<2R2,5:g00;L,12!sT'eW3W9o"). Qed.
Lemma PGSZ_eq : PGSZ = 4096.
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "###lp;1p;2g008Dj13Tg007Ej22!s/$_j11Tf0#1#1p=0g00Sjg00<Y#0!s$-3'2o"). Qed.
Lemma page_size_eq : ltac2:(zQ "30!hi5!hk3!hk8@3$0$1$2+hgg0").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "###lp;1p;2g008Dj13Tg007Ej22!s/$_j11Tf0#1#1p=0g00Sjg00<Y#0!s$-3'2o"). Qed.

Lemma round_up_pg_eq : ltac2:(zQ "40!hk3!hi5!hl4!hm6>1x$0@3$1$0@1$3^1@1$2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##@Ih01zh12H0h22H5h32Hah47__arithh54__ffh67__sat10h78__varmaph85__with94__x1h:4__x2h;4__x3h<4__x4h=4__x5h>1Hh?2H1h@2H2hA2H3hB2H4hC2H6hD2H7hE2H8hF6!t5$9hG1qhH2q0hI1rhJ2r0hK1xp;1p;2p;3p;4p;6p;7p;8g007_j1FTg008Dj1ATg00WBj14!s/$_j2GTg00X<j2O!s/$Zj28Tg00Y7j26!s/$Tj2;!se$bj1STg009Gj2_Tg00Z1j22!s/$Qj2[Tg00[2j1v!s/$Kj2Y!sS$dj21Tg00ADj2:Tg00\2j2VTg00@hj2L!s8$Yj2XTg00]?j2]Tg00Bkj2ZTg007Ej2J!se$_j2e!sA$Gj3d!sS$ej1<Tg00^Dj2T!s/$mj2cTg00_Vj3bTg00`?j1a!s/$]j2`Tg00a>j3H!s/$gj2RTg00bSj2UTg00CLj1}Tg00c?j3^!s8$lj1|Tg00DLj2\!sA$_j1{Tg00d=j4Q!sA$jj1zTg00EHj1yTg00F3j2B!s/$Vj2@Tg00HFj1u!s/$dj3tTg00G9j4C!s/$dj1r!sw$[j6qTg00e?j2p!s/$bj3NTg00fEj3E!s/$hj3oTg00Ikj2nTg00JMj2mTg00K9j3M!s/$Sj3lTg00L2j4kTg00gKj1j!s/$ij3iTg005Fj6KTg00hLj1sTg00iWj1hTg00jUj3w!se$dj7xTg00MHj7g!tC$Gj8fTf0R0#F#Fp=>f2R1f1R2'8/G0p=9g00SjR3?M20p=0g00S0R49M30p=P1L40p=51T30p=?Aw320p=3P3P2g00U4P0CCp=I!s4$MlR5g00NKR6P6g00NkR7P0g00OKFxp=7P1P5P6P6P7P2P0Fgp=W!sn&k>!sn%Df3R8!sK+1P2P0Gfp==P3g00<YR9#FR:#FR;#>!s$+AR<%42R=%A9R>,G0'O,8!sz$eR?=92>/6?/;?'0X03P3P<1G<>,O=,821820R=/G>/60/;0!sH&%40R@%A:RA%S9RB#>RC#ARD'_RE'2A92<>/6</;<,0=X03A90E>/[E%PER=#vRFA92E>RG16GE,;E12GE'8'0[1YGE114ERGA91E>RH/2ERI#511IE':[1VHE11E4RHA98E>RI/2ERJ,1E1LJ4':[1XIEf4RI?9E>RJ/6E#P\=1]JEf5RK!s;$L/2E/0L\=16LEP3f6RL?9E>/2EP3f7RM#4/[Ef8RN#4RO16O!tl%O!tl$\F1YOEf9#4RO/2ERF#511FE':\G1VOEf:!s?+!t`$F4':\H1XOEf;!s@$!t]'OEf<RO#4!uT$/0H\=16HEP3f=RH#4!tY$PKg00:@RF1Z4E'JPGeRPO1%50110E':PHP!s5$N11NE':1eAD114ARN%5DRPPG[RG[%5ARQg00SNRRAdAD2UW3%5E\R^3QP21Z4A,JFPNeO1PGg00THRGg00l]RN#<#<RF#<RQ#<RR#?RS1T3NRN'31c3<=b3NR<%<RRR#<RT#<#?%a9,`3RU%?RRR5H3%?FRF9H3U,3S'3'3'3g00m<RV'R'UAH3US/3N%?T%?Q/3F,3R'3,3</RV'U%}GRV5^G3^%|GRGP3P31\3IP1%{3R<CQP2!s7$KP8P<CQCQ%z3RR%y3RF1B34RQ1@3:RT'I,7FP3PTg00U[RN1B3A%uC5t3RCCC,7F5WF%r6RAPF!s$$!|X&1DCQ,7FEqR6PA1@39R9,p3%S:,@39N3C=E3T'D,7FC=PAPF1@3;R;,IQ!t;%;PNP!t++P!t%%6PAAE39C1B3>5o31@3BRB!sq&;!sq+AE39TAN3BC!s9&!s$%1nF7R7P0P1g00VBRBg00VbRC'J1m01=MBCdAl342CkR4b5b7b8X93X:3X;3X<3X=3%52112E':g00mh\=R=%411;ELR1/88'0[%5K11KE':181M,0J\=18IK1;LE'0[[[[^93^:3^;3^<3^=3P0PMPHf>PLfDPKPOPIfCO9b4b6bFb6b1b2bJbHbEbDbCb2bBbIbGbAb@b?b1b>%jD,O@PVPGP<PR1B3D!vY&7P!u5&PPP0b49i@DEKP?g00nEEKg00oPg010TEK%s0%h0'0eXK3o"). Qed.
Lemma mmap_len_round_up : ltac2:(zQ "40!hk3!hi5!hn3!hm6>1l$0@3$1$0@1$2^1@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01lp;1p;4p;3g00hLj15Tg00iWj14Tg011Zj10Tg012gj41Tg013Cj13Tg00K9j32Tg00SjR0P0f0R1#5R2%41%01C1%31=202eW0o"). Qed.
Lemma mmap_len_ge : ltac2:(zQ "60!hn3!m5!re!hk3!hne!s4>1l$3>0@2$1Z^1@2$2@2$5^2@1$0^2@2$1@1$0^2@2$4^2+hgg0").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##7<h02H0h14__x1h24__x2h34__x3h41Hh52H1h62H2h72H3h82Hlh97__arithh:4__ffh;8__varmaph<5__with=1lh>1qh?1rh@1zp;2p;1p;3p;4p;6p;7p;8g009dj21Tg007_j1>Tg008Dj1DTg00XZj20Tg00W_j22Tg00Y7j2<!s/$Tj2=Tg00@hj24Tg00ADj23Tg00ZQj2PTg00K9j35Tg00[2j1K!sA$1j29!s8$Kj2dTg00\2j2]!s/$Yj2YTg00]?j2WTg00Bkj2V!tg$Ej2G!sA$ej1ATg00^Dj2:Tg00jUj3;Tg00agj2FTg00`?j1U!s/$]j2T!sA$>j3STg00CLj1RTg00c?j3E!s8$lj1QTg00DLj2CTg00d=j4O!s8$jj1NTg00EHj1MTg00F3j2@!v>$bj1L!s8$Vj2?Tg00G9j47!s/$dj1f!sn$[j6eTg00fEj3J!s/$hj3cTg00ebj3ITg00Ikj2\Tg00JMj2Z!vP$Sj3[Tg00L2j4XTg005Fj6^Tg013Cj1_!sA$dj7`Tg00MHj7a!sn$Gj8bTf0R0#>#>p=8f1R1g00MlR2g00NKR3P3g00NkR4P0g00OKF`p=6f2R5P2P3P3P4P1P0Fap=Hf3R6!s;+5P1P0Gbp=Bg00SjR7g00S0R8/10P7g00<YR9#>R:#>#8!s$+DR;1050%D9R<'2/<0/=0R=,45105;R>,1='3X@7101;R=/2</P;A57;8R?#K12><R@1<@;,=;19@;'0557[1d@;118;RA106;/2<RB/9;RC,4811C;'3[1]B;11;8f4RB/0!sI$C/9;RD,1;14D8'3[1YC;f5RC!sE&D/<;=578\?1WD;f6!s=+9;=57D\?1<D;P7f7!s?%/9;P7PCg00:@1V8;'GPAeO11480110;'3g00THRAg00l]RC#ARD#ARE,:71:7DRD1:7CRC5;75;7g00m<RF'F%AE,:7%U9,T7=S7D=;7C5;7/FF%RA5EA3E%QAP71C75P11C76CO%N7%M7RAP71@78RFg00U4RC%L9,?7RDC7,6AP7PDg00U[RE1@7;RG!s<$5HA%f3RHPA!s$$!xR'7PGg00k>R3PF!sN$EePHP71?79R9=J7GRF1@7<5c7P31?7:R:9I7G=J7!t:%CBPHP7P9PCAI7:GR:!tP':PE!sw&5HACBCB1\A4P0P5g00VB!vG$VbR4'G1Z05=5A4dA[781CXb:b;b<X17X27X371485115!w$%mh\?1=;6/0B957@[1=6;R;,4511;>'3[[^17^27^37P0P5P6f:P1f8O5b9b0b?b>b7b6b5b0b4g00keg00nEE^%_1R6,41116='3eW8W=o"). Qed.
Lemma mmap_len_aligned : ltac2:(zQ "40!hk3!hi5!hn3!ho4>1l$0@3$1$0@2$3@1$2^1+hgg0Z").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01lh11zp;1p;2p;3p;6g008Dj16Tg00XZj25Tg00W_j24Tg00Y7j27Tg00YTj2;Tg00Z1j23Tg00K9j32Tg014Jj2:Tg005Fj69Tg013Cj18Tg007_j11Tf0R0#1#1p=0g00SjR1P1g00<YR2#0#0#0#0#0#0#6R3f1/50%62R2'4/70/;0/33g00S0R4521X111503/42/73/:3g00keg00nEE9%80/33=214eW0o"). Qed.
Lemma mmap_len_of_aligned : ltac2:(zQ "50!hk3!hi5!hn3!s4!ho4>1l$0>0@2$3Z^1>0@3$1$0@2$4^2+hgg0Z@3$1$0@1$2^3^3").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##;sh02H1h12H6h24__x1h34__x2h44__x3h54__x4h64__x5h71Hh82H0h92H2h:2H3h;2H4h<2H5h=2H7h>2H8h?2H9h@2HmhA7__arithhB4__ffhC8__varmaphD5__withE1lhF1qhG2q0hH1rhI2r0hJ1zp;2p;1p;3p;4p;6p;7p;8g00@hj26Tg007_j1CTg008Dj1MTg00Z1j21Tg00Y7j25!s/$Tj2;!sA$Qj2LTg00[2j1[Tg00XZj2@!s8$Kj2VTg009dj22Tg00ADj27Tg00\2j2T!s/$Yj2STg00]?j2QTg00Bkj2c!tU$Ej2R!sA$ej19Tg00^Dj2P!s/$mj2`Tg00_Vj3_Tg00`?j1^!s/$]j2]Tg00a>j3=!s/$gj2OTg00bSj2ETg00CLj1\Tg00c?j3N!s8$lj1ZTg00DLj2K!sA$_j1YTg00d=j4D!sA$jj1XTg00EHj1WTg00F3j2J!sJ$[j6oTg00Gdj1n!sA$Vj2B!vb$bj1UTg00ebj3ITg00fEj3F!sS$9j4HTg00MHj7m!sA$hj3lTg00Ikj2kTg00JMj2hTg00K9j3G!s/$Sj3dTg00L2j4eTg005Fj6bTg013Cj1fTg00W_j2gTg00jUj3a!sS$dj7i!t$$Gj8jTf0R0#C#Cp=?g00SjR1g00S0R27G0p=>f2R3f1R4'@/g0p=4AG140p=31P10p=:Aa!s5$0P1P4g00k>P0CHp=A!s4$MlR5g00NKR6P6g00NkR7P0g00OKFip=8f3R8P5P6P6P7P3P4P0Gjp=<1620R9g00<YR:#CR;#CR<#?!s$+MR=,14#>P1P=%M:R>9480/50/;0/38XJ1A43=>/L=%>=R?#[R@A48=>RA15A=,;=11A='@'3[1VA=122=RAf4RB?4=>RC/1=RD,6212D='7[1TC=12=2RDf5RE!sI$F/1=RG,2=16G2'7[1SF=f6RF!sC$G/5=#>\?1QG=f7!s9&1=/3G\?15G=P1f8RG?4=>/1=P1f9RH/L=f:RI15I!tk%I!tk$\@1VI=f;R@/1=RJ!t`$J='7\A1T@=f<RJ/1=RK!tU$K2'7\D1SJ=f=RJ!tP+J=f>RD!tL$D\?15D=P1f?!tF$PEg00:@1c2='RPAeRAO1120=,79PJPAO1162G12G='7g00THRGg00l]RA#9RJ#9R9#9RD#9RK#9RL#:RM%:JRJ1P1ARA'0RN'01`1==_1A%^:,]1RO%9L#:RL5=1%:K%:DRD%:9R99=1O'0!s$%g00m<RK'O'EA=1OMA=1OJ/0A'0A=1OD/09,0M,0L1ONK'E'E%\G5NG3N%ZGP1P11K1BP3%Y1RGCDP4!s7$EP8PGCDCD%X1%W1RGPGPG!z1'1J1=RK1J12RN'A,8GEoRL%n6RM1B1;R9%U;,B19I1K%U:,B1R;5F1!sO$C<PM!sp/P1PNg00U41B1<R<CH,8GP1P<g00U[PK!s6$Fm!sZ&LPMAF19K1J1>5l11B1:R:9I1K=F1<!t,-1A;N,8GPMAI1:K/A9!s@$!s$%1kG7P0P3g00VB!wc$VbR7'R1h03=GG7dAd124CebBbCbDX21X31X41X51X61g00mh\?R?1;=E/@8,33[162B12B='71;=8/@F,3C\?%>E1;B=/3E[[[[^21^31^41^51^61P0PBPIP8fCP@PHP4f@fAO9bAb0b1bIbGb?b>b=b1b<bHbFb;b:b9b0b7g00keg00nEEb%f3/33eW@W8XE1o"). Qed.
Lemma round_up_pg_ge : ltac2:(zQ "30!hk3!hm6!s4>1x$0@2$2^1@1$1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##6Fh02H0h14__p1h24__x1h34__x2h44__x3h51zh61Hh72H1h82H2h92H3h:7__arithh;4__ffh<8__varmaph=5__with>1qh?1rh@1xp;1p;2p;3p;4p;6p;7p;8g00iWj1fTg00@hj20Tg007_j19Tg008Dj1HTg00Y7j28!s/$Tj2;Tg00ZQj2STg00K9j33Tg00[2j1K!sA$1j25Tg00XZj2@!sA$Kj2eTg009dj22Tg00ADj27Tg00\2j2Z!s/$Yj2XTg00]?j2WTg00Bkj2V!t^$Ej2D!sA$ej1CTg00^Dj2>Tg00jUj3BTg00agj2TTg00CLj1RTg00c?j3Q!s8$lj1PTg00DLj2ATg00d=j4O!s8$jj1NTg00EHj1JTg014jj6L!ur$bj1MTg00FVj2<!s/$3j2=Tg00G9j46Tg00MHj7I!s8$dj1U!t$$[j6dTg00fEj3G!s/$hj3cTg00ebj3FTg00Ikj2^Tg00JMj2]!vb$Sj3\Tg00L2j4[Tg005Fj6ETg00hLj1YTg011Zj1_Tg00W_j2`!sS$dj7a!sw$Gj8bTf0R0#9#9p=4f2R1f1R2'@/`0p=1P2g00MlR3g00NKR4P4g00NkR5P0g00OKFap=:f3R6P3P4P4P5P1P2P0Gbp=?g00SjR7P7%f0R81020X57P7g00<YR9#9R:#9#4!s$+HR;%H9R<9120/80/;0,02X57A10;</S;g00S0R=937;R>#KA12;<R?18?;,;;15?;'@537[1e?;12=;R?A11;<R@/5;RA,0=12A;'7[1Z@;12;=A16;<RA/5;RB,2;10B='7[1XA;f4RA?1;<RB/8;=37=\>1WB;f5RB!s=$C/5;=37C\>18C;P7f6?1;</5;P7PBg00:@1V=;'DP?eO110=0120;'7p-0R?g00THRCg00l]RD#CRE#C,>71>7E1>7D5B75B7g00m<'T%RC3Q%PCP71A71P21A76CO%N7%J7RCPC!w9+!s0,BELP7%M9,<7RBg00U[1=7;RDC6,:CFI%U4REPCP!sc/7PDg00k>R41=7=!sO$EdPEP71<79R9=G7D1=7<5c7P41<7:R:9F7D=G7B!sR$C?PEP7P9g00U4AF7:!t:%C?C?1^C5P0P1g00VB!uj$VbR5'D1]01=3C5dA\7=2C[b;b<b=X27X37X47W1121;,76g00mh\>1;;6/@A937@[1;6;,01[[^27^37^47^1?P010=1P1P6f9P2f8O6b:b0b?b>b9b8b7b0b6g00keg00nEEE1008e%Y0%_0EEW@o"). Qed.
Lemma round_up_pg_aligned : ltac2:(zQ "40!hk3!hi5!hm6!ho4>1x$0>0@3$1$0@2$3^1+hgg0Z@3$1$0@1$2^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##<4h02H0h12H5h24__x1h34__x2h44__x3h54__x4h64__x5h71zh81Hh92H1h:2H2h;2H3h<2H4h=2H6h>2H7h?2H8h@2HxhA7__arithhB4__ffhC8__varmaphD5__withE1qhF2q0hG1rhH2r0hI1xp;1p;2p;3p;4p;6p;7p;8g007_j1CTg008Dj1NTg00Z1j21Tg00iWj1mTg00Y7j25!s/$Tj29!sJ$Qj2LTg00[2j1[Tg00XZj2?!s8$Kj2WTg009dj23Tg00@hj26Tg00ADj27Tg00\2j2T!s/$Yj2RTg00]?j2STg00Bkj2bTg007Ej2V!sA$ej1;Tg00^Dj2O!s/$mj2`Tg00_Vj3_Tg00`?j1^!s/$]j2]Tg00a>j3=!s/$gj2MTg00bSj2FTg00CLj1\Tg00c?j3K!s8$lj1ZTg00DLj2Q!sA$_j1YTg00d=j4D!sA$jj1XTg00EHj1qTg00F3j2J!sJ$[j6pTg00Gdj1o!sA$Vj2>!vt$bj1UTg00ebj3ETg00fEj3I!sS$9j4HTg00MHj7l!sA$hj3kTg00Ikj2gTg00JMj2fTg00K9j3G!s/$Sj3eTg00L2j4dTg005Fj6PTg00hLj1cTg011Zj1hTg00W_j2iTg00jUj3j!s\$dj7a!t1$Gj8nTf0R0#C#Cp=Ag00SjR1g00S0R27G0p=Bf1R3=G10p=2f2R4/?3/i0p=41O10p=:Aj130p=0P1P3g00k>P0CHp=@!s4$MlR5g00NKR6P6g00NkR7P0g00OKFap=8f3R8P5P6P6P7P4P3P0Gnp=<g00<YR9#CR:#CR;#A!s$+NR<,10#BP1%m3R=1204X71P1P<%N9R>9440/50/90/24X71A43<>/L<%B<R?#[R@A44<>RA15A<,9<11A<'?'2[1WA<132<RAA48<>RB/1<RC,6213C<'7[1TB<13<2RBf4RC?4<>RD/1<RE,3<16E2'7[1RD<f5RE!sC$F/5<#B\?1SF<f6RF!s;$G/1</2G\?15G<P1f7?4<>/1<P1f8RG/L<f9RH15H!th%H!th$\@1WH<f:R@/1<RI!t`$I<'7\A1T@<f;RI/1<RJ!tU$J2'7\B1RI<f<RB!tP+B<f=!uG$/2B\?15B<P1f!tF%PEg00:@1b2<'VPAeRAO11620130<'7PBP!s6%G13G<'7g00THRGg00l]RA#;RB#;RJ#;RK#;RL#;RM#:RN%:BRB1O1ARA'0RO'01`1<=_1A%^9,]1RP%;M#:RM5=1%:L%:KRK%:JRJ9=1P'0!s$%g00m<RL'M'FA=1PNA=1PB/0A'0A=1PK/0J,0N,0M1MOL'F'F%\G5KG3K%ZGP1P11Q1CP4%Y1RGCDP3!s7$EP8PGCDCD%X1%q1RGPGPG!z9'1J1<RL1J12RO'@,8GEpRM%o6RN1>1:RJ%U:,>19E1L%U9,>1R:5I1!sO$C<PN!sp/P1POg00U41>1;R;CH,8GP1P;g00U[PL!s6$Fl!sZ&MPNAI1JL1J1>5k11>19R99E1L=I1;!t,-1@:O,8GPNAE19L/@J!s@$!s$%1gG7P0P4g00VB!wc$VbR7'V1f04=GG7dAe123CdbBbCbDX21X31X41X51X61g00mh\?R?19<E/?8,24[162C!{\%19<8/?F,2D\?%BE19C</2E[[[[^21^31^41^51^61P0PCP@P8fBPIPHP3f@fAO9bAb0b1bHbFb?b>b=b1b<bGbEb;b:b9b0b8g00keg00nEEP12=3e%c3%h3EPW@XI1o"). Qed.

Lemma elo_went : ltac2:(zQ "80!hk3!re!hi5!hs9!ht0!s4!m5!ma>1b$0>1n$0>0@2$1@2$5Z^2@2$6^2@2$7+2+k0@3$2$0@1$3@2$4^3^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01bh11np;2p;1p;4p;3p1003<p4p70R0p1015Np4p710R1p8P0p1016Np4p7210R0p8p1006Ap4p70R2P1p8P2P0p8g00@hj2?Tg007_j10Tg008Dj12Tg009Gj24Tg009dj2>Tg00ADj2;Tg017Rj2:Tg00HFj15Tg018^j16Tg019Aj11Tg01:Aj47Tg005dj38Tg01:aj29Tg00K9j33Tg01;Kj2=Tg01<Mj1<Tg00SjR0g00S0f1R2'?g00<Y#0R1#2%01#0#0#0#0R1#2'4,>2';f2R3f0':%51R1%61R1P1P1%13%12C7781'9=303e1=32#<=303eUX10W0o"). Qed.
Lemma ehi_went : ltac2:(zQ "91!hk3!re!s4!m5!ma!hi5!ht8!ht0!hne&@2$1@2$2Z^2@2$3^2@2$4+2+k0>1b$0>1n$0>0~0>0~0@3$5$0@1$6@2$7^4^3@2$8^4^3").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01zh11bh21np;2p;1p;3p;6p;4g00@hj2DTg007_j11Tg008Dj14Tg009Gj2:Tg009dj2CTg00ADj2<Tg00HFj1;Tg01=Nj25Tg01:aj20Tg00XZj22Tg00K9j33Tg007Ej29Tg017Rj27Tg005Fj68Tg019Aj16Tg018^j1BTg01:Aj4=Tg005dj3>Tg01>4j3?Tg01;Kj2@Tg01>Qj1ATg00SjR0g00S0f1R1'Dg00<Y#1R2#4%12#1#1#1#1R2#4':,C1'<R3P0f3R4f0R5%;2R21524'0R6'2f4R7/24R8530X00P0f2R91275=308X001249R8,901529,021795E8P61741E8%64R1,02%69R6,02'2=308e%B2R5P5P5P1P6C=R67>5,02A?556,02'2=308e1@49#A=308eV3UX20W1o"). Qed.
Lemma elo_pair : ltac2:(zQ "70!htf!ig4!ii2!hi5!hk3!hs9!iia>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$3$4@1$5@4$2@1$1@1$0#k0@1$1@1$0#k0^2^1@2$6@1$0#k0^2").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01ah11np;1p;2g007_j10Tg00HFj14Tg018^j12Tg01:aj21Tg007Ej23Tg00<Y#0#0#0#0#0#0#4R0#2R1g00Sjf1,10'3X11W0o"). Qed.
Lemma ehi_pair : ltac2:(zQ "80!htf!ig4!iia!ii2!hi5!hk3!ht8!hne>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$4$5@1$6@4$3@1$1@1$0#k0@1$1@1$0#k0^2^1@2$7@2$2@1$0#k0^2@2$2@1$0#k0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01ah11np;1p;2g007_j10Tg00HFj15Tg018^j12Tg01:aj21Tg00XZj24Tg007Ej23Tg00<Y#0#0#0#0#0#0#5R0#2R1g00Sjf1,10f0,10'4'3X11W0o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdisj_In : ltac2:(zQ "91!htf!ig4!ij9!il4!ila!hi5!im2!im7!in0&@2$2@1$1@1$0#k0@1$1@1$0#k0>1l@1$4~0>2e1~0>2e2~0>0@1$8^3>0@3$3~0^3^4>0@3$3~0^3^5@2$6@3$5~0^5^4@2$7^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##=fp'0h01Hh12H0h22e2h31li001lh42H2h52e'h62e1h72H1h82H3h92H4h:2Hph;4__x1h<4__x2h=4__x3h>4__x4h?2e0h@2e3hA1DhB2IHhC7__arithhD4__ffhE8__varmaphF5__withG1ei011ehH2l0hI1pi021pp;1p;2p;3p;6p;4p;8p;5p;7g007_j15Tg00HFj1ZTg018^j1STg01?Rj2KTg00ClR0j1GTg01@2R1j16Tg01A8j31!sE$Lj1?Tg00c?j32Tg00K9j30!sJ$Oj68!s/$kj2HTg01BJj24Tg01CMj6FTg007Ej2;!s8$jj3UTg01DDj3DTg00DLj2A!t$$_j1TTg00d=j4B!sA$jj1RTg00EHj1QTg008bj1PTg00FVj27Tg00G9j4>!s/$dj1OTg00IGj8N!s/$kj2JTg00JMj2L!u&$Sj3MTg00L2j4ITg00@hj2:!t^$^R2j29Tg01<Mj1ETg01>Qj1@Tg005Fj6CTg01E8j5Y!sg$dj7X!s8$Zj7WTf4R3f3R4f2R530f1R6f0R7'4'9p=31467,95p=VP6g00MlR8g00NKR9P9g00NkR:P7g00OKFXp=<P5P8P9P9P:P6P7FWp==g00<YR;#5R<#5R=#5!s$&Z#SR>/K>R>#GR?P>%65A1>54A1>53P>P3P4P3P4D3[[[^2>^6>R@X3?%?>RA#6A1>5ARBg00mhRCP>f5RDP3PDP3D3P6n010!s#%X4BW7W:X2>X6>A2>34RB#6A2>D3RE91>5f6RF=2>DRG91>5P1f9R1f8RH52>RI90?6P>f7RJPFPJPFD3RK[P5A2>JFRL90?AA2>HJRM90?AP?PAP0P>p-0!v1$SNPCn101!tY%2!s%$!tb%??g01F>PIP7E8PC1HK7b1W0P7O1W0A1>76RK1446RC[^5>%66RIA2>45f?RAf>52>50?f@RN=2>A90?BP?P?P0P>P?P7PDP7!tD2102100X@?PEfARE=2>NP7EFA0?3NP?P>!sa$>P7PJP6!sa<GfBRG=2>EP6EFA0>FGfCRG90>JP7fDRJ90>HP>fEREA0?1ER0f;RN91>7P!u;&NP>fFRNPEPNPED3]1]0[XI>A0?HJP7P0P?PNfJR0/46\K^5>P>fGRKPNPKPND3RH^1I]0X3?A1>7KfIRI/46!t$%KP2A0>INfH!xA$NPHPGA0>0KP>fKRG!uQ$EP7PED3X6>!sS$GKRHA1>K0RNfLRC=0>ERB?VCEPJP>fMRAP>fNROP7POP7D3X2>A0>AA14AA1;>A3U!x&%X0BP7O1A1>EGRPA0>AI14AIPDPIP7O23DW4P7O1n20!zO'2!s-$!s'$PEP7E8!xe%A1>KIP2PHPNP>PIPEPIPED3PJP>PAP>PGP7PG!tX,0A140APDP0P5O214A0g00SjRAg00THRJ#?%GJPAPA1AA3P5%TACBP61AA4CB%RA%QARJ!}_+A%P;,7Ag00U4R817A=C>,<JR=PA17A;P817A<!s9%<5=J%O9A=J<=GN1JJ:P7P5g00VBRJg00VbR:';1L75=0J:dg00S0=MA6CIbDbEbFX;AX<AX=AW>1:541:76'91:651:43'9[^;A^<A^=A^>AP7%ECfORA#@%EA%@CP6O5bC14GOebA3D!wH0PGP0PIP3P5P7O5X4P!w=41!w='W7!sB91000W9W8f:P7ECb9W1P1!s0$!}P&b!s+&W8P7P5P6O3W8W1W0XH?X?>P4P5P6P7O4n!xR&!|R%141!|`+000A0?7MP>PFPDPFPDD3[X3?PLO1P71;?M!t-$4!#4_+XB@X3?XG>P7DYW3o"). Qed.

Lemma region_free_app_r : ltac2:(zQ "92!htf!ig4!ij9!ina!ila!io2!hi5!ioa!ip8&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$6$3@3$7@3$8~0^4^3^2^1$5@3$6$3@3$7^4^3^2$5").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##-,p'0h01ah11Hh22l2h31nh42l1h52IHh62_Hh71eh81lh92szi001bi011pp;1p;2p;3p;4p;5g007_j12Tg00HFj1ATg018^j1<Tg01?RR0j29Tg00Clj1@Tg01FZj31!s8$Lj1;Tg00c?j36Tg01:Aj4:Tg01G7j44Tg01H0j15!s/$Nj37Tg01IHj3?Tg00ADR1j2>Tg01E8j5=Tg00K9j38Tg00VBR2f2R3f1R4f0R537g00VbR638p=0A8256p=3g00<Y#2!s$-A#<R6/96R2#@R7P2f3R8=123?045A0834R9[^36^06^27R:X47%;2!sG'P5W1X36X06X27P0P6P6f5R0f4R;56!sL,!sh-\:^87P5!sP$6R9P0C:=62;!sQ+3P4f7R<P9C4#5R=A1208?734R>;?5%3=%3>'>P1P8P3f8R1P<C4#5#3A129;?083A00;8P5P0P;f:f9R;!sF+;<?090P;P1P<P9P5O4W1W6P4P5O2n20010!s#$12!s-%0b1!uR-X5:X47X96X7!sY/10!s$$211!sf$X02P5D=W4o"). Qed.

Lemma region_free_InZ : ltac2:(zQ "e1!htf!ig4!iia!ij9!hne!s4!ina!ila!ii2!io2!hi5!im2!ioa!il4&@2$3@1$1@1$0#k0@1$1@1$0#k0>4maps@1$7~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1e@1$1@1$0#k0>2sz@1$1@1$0#k0>0@3$a$6@3$c^5^4^3$9>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^3^2^6@2$b@2$5@2$4@2$2@1$0#k0^6@2$2@1$0#k0^5@2$2@1$0#k0^4@2$5@2$4@2$2@1$0#k0^4@2$2@1$0#k0^3@2$2@1$0#k0^6").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##ISp'0h02H1h11Hh21Eh31ah41bi001bh54__p1h64__x1h74__x2h84__x3h91eh:1ni011nh;2szh<2H0h=3Hinh>2e0h?1li021lh@4mapshA1ri031rhB2H3hC7__arithhD4__ffhE8__varmaphF5__withG2e1hH2n0hI3sz0hJ2H2hK2H4hL2IHhM2l0hN2n1hO1pi041pp;1p;2p;3p;4p;6p;8p;5p;7g007_j1<Tg00HFj1mTg018^j1\Tg01?RR0j2ZTg00Clj1TTg01HNj3:Tg01:Aj42Tg01A8j3;!s8$aj20Tg00XZj21!s\$Lj1GTg00c?j3CTg01G7j49!sn$0j1FTg01IHj3hTg00ADR1j2cTg00@hj24Tg00K9R2j33Tg01CMj6M!sW$kj2LTg009dj27Tg01JNj2?!s/$kR3j2K!td$Oj6[Tg01D^R4j2@!s:$kj2YTg00[2j1ITg00DLj2HTg00d=j4E!s8$jj1XTg00EHj1WTg008bj1VTg00FVj2BTg00fEj3NTg00G9j4D!s/$dj1lTg014jj6kTg00Ikj2jTg007Ej2OTg00JMj2g!uK$Sj3fTg00L2j4e!v=$_j1bTg005Fj8Pj6QTg01E8j5`Tg01KNj2d!sV$dj7_!t|$[j6^!sJ$Zj7i!t=$Gj8]Tg00VBR5f0R6g00VbR733p=5f4R8f3R9'4f2R:f1R;'1/46'@p=8%F6=357p==14:;/@6p=>1d;6#F!s=%611:;/46p=JP;g00MlR<g00NKR=P=g00NkR>P6g00OKF_p=AP;P<P=P=P>P6E^p=UP:!s7+;P6Fip=SP9!s9+:P;P6G]p=R14;6,@:p=ag00<YR?#<R@#<RA#<!s$&mRB#\RC/ZCRD#TREPDA:89:#5PCPCP:P;C2RFf5RG5;D10BGRH10B8RI'1RJ10B9RKPK10B:PHD8RL[[^;C^9C^:C^3CRMX@E%GDRN?:9:#5A;DFNg00mhRNf6RO,0BRP/1HPIPIPKPPD8P6n010!s#%W=W1X;CX9CX:CX3CP0PCPCACDOG!su%f7RK=CDO9;DFP!tI2\M^?EP6!u;$KPOC2=CD!s]&PCPCf8RLPKC2RI!sg+GP8f9RFPLC9#FRQA:KG8RR;h;%5Q%5R'cP1POPGf:R1PFC9#=A:LOG#510BKRO/1P14JO7>HP6PLPKf<RHf;RO!sO%OFL#5P4!tH$>R4f=RJC2=3DIA;DIH10BORI10B1'110BFRPPP10BLPID8PG!s[$?RPP4C2!uE$FPLC2RR53DP2PD!sE$@R2PPC2RQ!sG$HPOC2RS93D;10BPRT10B4RU!t'$JRVPV10BHRWPTD8[!vA&1PFC2RT93D!si$fARQP2!t>&OP1C2RX53D!t<$!wL$PCP6P6n2001104000120100100XG!ta%BRYPQC2PSP6EMA3CQO!sd2;!sd?CR0PYC2RS!sS$JPHC2P;!sn$0JfDRZ=3C4P6fER4=3CPRPPCP2fFR[=3C2R210BZR\10B0R]!ul$YR^P^10BQP\D8[X4CP6P2PCPQ!v8$Q/1\R\P]P]P^PQD8X4CPCPYP4PZP6fHR^C9#=!tW$;fIR]!v5&ZP0C253DfGR2,0BR_10B[R`'1Ra14\_7>Q]2]0X>!sP$PYP2!sl+0P^!xl$S!s2$2P[P4P6!sD+[P;!t0&[P4!t0$10B]RS10B^RY'1R\14aS7>_!t,$I!sM$!t[$!sg'4PZC2RZ=3DZ11`QR`,LY17Y`1?Y`'K1?SaP5P3fJ,0BRS11Y_'7fL,0BRYfK!u?$'1,?SRa,6;fM,0BR`/1YRQP_P_PSP`D8]0P;17_\R\167a1L_QRS17_Q1?_Q'KRQfN!sm$/1`,?YRY!t<$!~J$Z/1_,7`R`167;fR,0BR4fQ,0BR0'1fP,0BRb11bZRZ/443>Rc!t8&ZRZ1677P5g01KlR_P5p-0RdP6PNg00SNn01!#3;$20000X>5g01F>P7P6E[PNfS,0BRB?J40ReAJ0bBRf'@/Y6b1W0WMP6O1%IZRg167_g00SjRhg00THRi#GRj%TiRiPh1Hh:RkP;1Hh9RlCE%XhRm%WhRnPh%V?,BhRog00U[Rp1Bh?R?1Bh@5NhR@CD,An,Un%l=RqPhP@g00U4R@Po!s@$Pn!#7]'GEkRG5SnCR1jn>R>P6P:1O571g6:#5dg00S0=fh;CeR=bDbEbFX6hX7hW8X5d116;,7:PN[11;:R<?>98[^6h^7h^8h^5dP6PfP0P4PBP:O5bCW0WHP6O1n102!}3$300021010211101P:O1b4bAW0W?!vB%\16_aPSPQP!xB$P`16_;P!wk%6_7PjPiPhPhPlP9%bhCEP;PkCEPmPnPhP?Pp1BhA9NhoRo!v2'PqPhPoP@P?!s8$9SnGCRP>P!uU0X8hX5d176<!uS$:9=a8;!uQ3ePbP0PBPKO5bCRKW0X?ZP6O116__PKW0XNg!uc61!uc6H!sN@9!sN&2W0P]P9P;P6GP!s4$^P9POPLGPP2P6EQbKXBPP[!s1$BW<P6O1b!s+&W1P6O1W1n2!w7$4!zy$0101A3D6X11UVPWPWPIPUD8[XODPTO1P61ODXO1b1W2P6O1A;DRJPJPHPOP1PFP:P6O6W=!u2$20!#<2&2!{~$!s3$WJW0P;P6O2!sF-12!s/&b1!#<\2XLMX@EXICX>C!s^-1040101!t#$100X3DP6D`W@o"). Qed.

Lemma region_free_intro : ltac2:(zQ "e1!htf!ig4!iia!ij9!hne!s4!ina!ila!ii2!io2!hi5!im2!ioa!il4&@2$3@1$1@1$0#k0@1$1@1$0#k0>4maps@1$7~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0>1e@1$1@1$0#k0>2sz@1$1@1$0#k0>0@3$d~0@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1^5@2$b@2$5@2$4@2$2@1$0#k0^5@2$2@1$0#k0^4@2$2@1$0#k0^3@2$5@2$4@2$2@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^5@3$a$6@3$c^4^3^2$9").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##=$p'0h01ah11eh21li001lh32szh41bi011bh51ni021nh61Hh74mapsh81ri031rh94__p1h:4__x1h;4__x2h<4__x3h=4__x4h>2n0h?2IHh@7__arithhA4__ffhB8__varmaphC5__withD2e0hE2l0hF2n1hG3sz0i042Ini052l'i061pp;1p;2p;4p;3p;7p;6p;5p;8g007_j17Tg00HFj1aTg018^j1UTg01?RR0j2PTg00ClR1j1KTg01:Aj4;Tg01A8j38!s8$aj20Tg00XZj21Tg00@hj29Tg01D^j2<Tg01HNj3>!sp$Lj1LTg007Ej2JTg00c?j3ATg01G7j4X!sS$0j15Tg01KNj22Tg00K9j36Tg01Cjj3VTg01Ikj2HTg009dj24Tg01JNj2@!s/$kR2j2GTg00DLj2F!t3$_j1TTg00d=j4E!sA$jj1RTg00EHj1QTg008bj1OTg00FVj2=Tg00fEj3DTg00G9j4?!s/$dj1NTg01EZj7MTg014jj6STg00Ikj2`Tg00JMj2_!u+$Sj3^Tg00L2j4]Tg00[2j1I!v7$Dj3\Tg005Fj6Y!sw$8j5Z!sS$dj7[!sw$Gj8WTg00VBR3f0R4g00VbR536p=:1245=635p=3f1R6g00MlR7g00NKR8P8g00NkR9P4g00OKF[p=Bf3R:P7P8P8P9f2R;P6P4GWp=Cg00<YR<#7R=#7R>#7!s$&aR?#UR@/P@RA#KRBPAP@P@P6P4C;RCf4RD58A10?DRE10?:RF'110?;RG'910?6,1GRH/9E'<RI[^3@^1@A>:;6#:[^5@^0@RJX7B%LA98ACP!sI'1J35RKW6X5@X0@P0P@P@f6R0f5RL5A!sR1AAALD?>!sy-\J^2BP4!s[$7RMP0C;=AAL!s\0P3P5P:P;PMP0CX#5RI/24#:X43P4P0PL!u[$0PLC;RN=6ANp-0RO^2B^0AP1PAPO!vs$mhA6A6:PDP:P4O2'<n10110000020020!s4$5X2BX0Ap?1001104PNPDO21JAN3VO310?0R1,9H10?LRH,11/9G'<10?MRG/11RP,HF14FP1@FP'Gf8RF,0?RQ/1GRG,@EP3P2f9RE,0?RR/1QRQ,4Hf;,0?RH/@PRS,26#5#3P6f:,0?/1RRR,41R11HHPRT14HP/GSRSf<,0?RP/@GRG!sz$=,0?/4QRQ125!sh'>!s:$RRRg00SjRUg00THRV#L%KVPUPU1FUDP;%TUCEP61FU:CE%RU%QURVPU%O<,=URWg00U[RX1=U<R<1=U=5DUR=C?,BV%N8RYPVPUP<PX1=U>9DUWR>!sB$PYPVPV!zz'PUP=g00U4R=PW!sF%UP>P=P<!s3$FM!sU$!sS'0ESC!s#$1`V9P4P;PK1_4;#:dg00S0=^U6C]bAbBbCX:UX;UX<UW=X9O1146,4;11:D,4611;:/9D11DL/9;'<PM[[[^:U^;U^<U^=U^9!y-$1KlRO=635f?,0?f@,0?PHPPP6PLPEO8b@1255#5#3eWEP4O1%IRRLPK125O!s<%>P4O1n102!yW$300021110010102b4b8W2!s^%1PTPSP!ww$PQ12O!wo&PK12O!t0%X2RP4O1!s8$!t+%XFL!t,60!t,0!tO<1!sH&%3Ieb6A>D;6!|U$6A8AC0!s1%!|J$EPFC;!s0$;P6C;RF56AA8AFM;\4O3UX3@X1@O3EYAAAN!}v&e!~P'X?JX7BXG@XD@P6P4O2n2!|K$6010121!td$1X0AP4DZW7o"). Qed.

Lemma region_free_disj : ltac2:(zQ "f1!htf!ig4!ij9!iia!s4!ina!ila!io2!hi5!im2!ioa!ht8!hs9!il4!hne&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$6~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1e~0>0@3$8$5@3$a^4^3^2$7>0@3$d~0^2^5@2$9@2$4@2$e@2$3@1$0#k0^5@2$3@1$0#k0^4@1$c^3@2$4@1$b^3@2$3@1$0#k0^5").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "p'0h01Hh13Hinh21ah31eh42e0h54mapsh61nh72szi001bi011pp;1p;2p;3p;4p;7g007_j10Tg00HFj1ATg018^j1<Tg01?RR0j2;Tg00Clj1@Tg01HNj39Tg00K9j38Tg01A8j36Tg01:aj21Tg00XZj24Tg01<Mj15Tg00@hj22Tg01>Qj17Tg01D^j23Tg01:Aj4:Tg01LLj7?Tg005dj3=Tg01>4j3>Tg00<Y#0#0#0#0#0#0#AR1#<R2/;2R3#@P0P2P2g00VBR0f4R4f3R5f2R639g00VbR738f1R8f5R95631119R:1114'4%56'2%76/2:'3[[f0R:f7R4f6;99=807P2P2P6P8C:f8R7563f9P7P4P5P6P8P:F?1117R71114'4R4P2P2P5P6C:R69=22,11R5'2A>226,11,45/27'3e%56,24%76/27'3eW1W0X72X32P8P:O2n2001101000121100100X43X62X22W5o"). Qed.

Lemma vmwf_cons : ltac2:(zQ "h12!htf!ig4!iia!ij9!ipf!hne!ina!iq7!ila!ii2!io2!re!hi5!ioa!s4!m5!ma&@2$3@1$1@1$0#k0@1$1@1$0#k0&@2$5@2$2@1$0#k0^3@2$2@1$0#k0^2>4maps@1$8~0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@1$4^3>0@2$b@2$f@2$2@1$0#k0^3~1@2$e~1@2$h0+2+k0>0@3$c$6@3$d^5^4^3$a@1$4@3$7~0@4$9@1$1@1$0#k0@1$1@1$0#k0^5^4^6").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##<'h01eh11Hh26__sat1h34__x1h44__x2h52Hah63Hinh77__arithh84__ffh9!sY%0h:8__varmaph;5__with<4__x3h=4__x4h>2Hbh?2Hnh@2HphA3HrfhB1ahC2e'hD4mapshE1np;1p;2p;3p;4p;7p;6p;8g007_j14Tg00HFj1jTg018^j1YTg01?Rj2RTg00Clj1LTg01MZj1JTg01A8j35Tg01<Mj19Tg01>Qj18Tg008Dj1HTg009Gj2QTg01@2j1@Tg01:aj20Tg00XZj22Tg01HNj3K!sA$Aj46Tg00c?j3ETg00K9j3?Tg00A_j2Z!sw$dj2BTg00@hj21Tg00BGj3X!s/$kj2WTg007Ej2I!u&$Lj1VTg00DLj2>!t$$_j1UTg00d=j4D!sA$jj1TTg00EHj1PTg00FVj2:Tg00fEj3GTg00G9j4F!sA$3j2O!vG$dj3NTg00MHj7S!sJ$dj1iTg00Ikj2hTg00JMj2g!u<$Sj3fTg00L2j4eTg005dj3<!vP$4j3;!vk$Oj6`Tg01N\j6_Tg01D^R0j2=!vm$bj1^Tg01EZj7]Tg01BJj2aTg01Okj4bTg01Q1j4\!vI$DR1j2c!t>$dj7d!tb$Gj8[Tf3R2f2R3'Bf1R4f0R5'1'cp=3g00VBR6g00VbR77?5p=AP4g00MlR8g00NKR9P9g00NkR:P5g00OKFdp=7g00SjR;!sR$U4P5CFp=CP2P8P9P9P:P3P4P5G[p=Mg00<YR<#4R=#4R>#4!s$%R?#jR@#YRA/RARB#L%J3P1f4R195B5%94RC%84RDPD%H=RE%H?R?'QRFC3RG[^0B%@210@2RH10@3,2HRHPHPFC3f5RH?K12#APAPAPHP1C6f6RI5EB#J[[P5A5B5IP!sj&I10@IRJ10@H,2JRJPJ!sj$8RJf7RH;KI!sm%f9RKPJC6f:RL5EB95B5RM!sj%!t4$JPHC6RJ=EBK#@P0!s:$LPKC6=?B4f;R095B4%93%83RGPGPFC3P5!sL$0PLC6RG=?B3P!sr$f<RNP0C6RO%95%85RPPPPFC3X0B1ZE?RPg00S0RQ/BERR11Q?1BQF[RS[RT11QERUg00SNRVAXE?4UW5R?11QF\V^5URU!wu$:@1WQE'IPReO1RRPSg00THRV#VRW%LVRVP;1>;3P4%U;RXCD%T;RY%P;RZPZ!xN+;1:;<R[g00U[1:;=9G;[R=CF,7Z1O;E=N;@,C=,7ZFSRE%i9R\PECM1hZ:REP5P31I671g53#AdAf;Q4CeRQb8b:b;X3;X4;P51254R7P7!vK$41243R6P6PFC3[^3;^4;P5f?,0@R]f@,0@PKO3b7b2b9b2A<AAO,0@R^A;!s0%,2^R^P^PFC3e%9O%8OROPO!s5$P2P5E`W1P5O1A5B3NPHP2P5O2W6P5O1n20010!s#$2110!s3&X1MX0BPJPKA5B5LP0PLPKP4P3P5E_10@LRL10@K'2/1C11DL'=PPPTP?PUPRPSPWPVP;!w,$1P3PXCDP41>;2CDPYP!w+-%^<,:;R<!vh%1:;>9G;</C[,7ZF]RZP\PZCMPEP!vY0X<;X=;11731232/15'=11621221/14'=!v]&^<;^=;P5A;AAI,0@A<!s-%f>,0@P]P1O5!vn/G,0@R1A;!s0%'!s:$3!wE$'!s<$3!w+$]/11'=e1aG3eb1W6XCBP3CbC\WAW?W@W>P4P5O2!vs-12!s/&W1XEAXBAWDo"). Qed.

Lemma pwdisj_filter : ltac2:(zQ "71!htf!ig4!ij9!in0!ina!ila!iqf&@2$2@1$1@1$0#k0@1$1@1$0#k0>1f>0~0$4>1l@1$5~0>0@1$3^1@1$3@3$6~0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##6pp'0h01Hh11li001lh22H0h32e'h42H1h53Hinh61fh71Ah82H2h92Hph:2e0h;2e1h<1xh=2IHh>2_Hh?1bi011bh@1ei021ehA2l0hB1pi031pp;1p;2p;3p;6p;4p;5g007_j15Tg00HFj1ETg018^j1@Tg01?Rj2>Tg00ClR0j1;Tg01@2R1j11Tg01QLj34!sE$Lj1?Tg00c?j32Tg00K9j30Tg01AOj6=!s/$kj2<!s/$8j33Tg01BJj27Tg01CMj6:Tg00ADR2j28!t&$gj4DTg01Okj4CTg005Fj69Tg007Ej2ATg01E8j5BTg00VBR3f0R4g00Vb30p=6g00<Y#5!s$-E#@R5/>5R5P3[%;5R6P5%14R7f3R8f1R9545#1[X16%?5R:#1g01REW9f4R;=459#1\7f2R7=259#1P1f5R1=25;R<9069f8R=f6R>=251R?!sq$R@[P4A2587RA906:A25;8RB906:P6P:P0P5p-0P4g00SNg00mhR:n1011000002!s%$!s#$X:6g01F>P<P4E=P:1<@4b2W0P4O1W0A3549R@1789R:[^35%19RCf;RDf:RE525906Af<RF=25D906BP6P6P0P5P6P4P1P4!tB2103100X;6P<f=RG=25FP4E:A06;FP6P5!sa$5P4f7R0P9!sc<?f>R?=25GP9E:A05>?f?9050P4f@R?905=P5fARGf9RF=06GRGA354DP!u9&DfGRDfER:fDRH525!vp%I]2]0[XB5A06=?P4PGP6fBfFRG/79\@^35fHR@A25G:!sW$^2C]0X16fCRC935417:9!t-%CPDP:O1P3!s$$6P4fIRC=45GR?925DP?n0!uM%!wL%#1P4PGA45@:A354?g01SKp4p710R?P3\4R3%;7R:P2A48749389A3;79P8P7O1#6'8[RGA3894P7P9!s8%A4;8993;7RD[A3187P;P8!sA%\DP8P7P9P4CDP9n20!t['1!y&'W1X<9W6W7PG^1:^<9^63^7?P4P5fKR?P7P@P9O5A357@P?!tS'P2A358CfL!t7%17?;P4A351?fOP>O1#6PEP0P9O2W>W5P9P4O2!tL7b5b0W5X35PHP9O1RHCCPHn011!sP$20100b?PIeW8W4PEP4E9b8W2PF!s0$!zx&b!s+&W4P!v3%3W4W2W0XA6X:5!uv'O4n02!tM&!t$$411!s7-A064BA450<!}q%PAO1P41A6B!t%$9W=X16X@5P4DBW1W6o"). Qed.

Lemma vmwf_remove : ltac2:(zQ "60!htf!ig4!ipf!ila!ij9!ir9>4maps@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>0@1$2^2@1$2@2$5^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##0Yh01eh13Hinh21ph31Ah41Hh51fh61lh71xh82Hbh92Hph:2_Hh;1ah<4mapsp;1p;2p;3p;4g007_j14Tg00HFj1HTg018^j1DTg01?Rj2BTg00Clj1@Tg01MZj18Tg01A8j30Tg01<Mj1>Tg01>Qj1=Tg009dj2<Tg008Dj1;!s8$Gj2ATg00@hj2:Tg00ADR0j23Tg01@2j19Tg01Sgj2?Tg005dj37Tg01T`j35Tg01H0j11Tg01QLj36!s/$gj4GTg01UMj3C!s8$1j4ETg00K9j3FTg00VBR1f0R2g00Vb3Fp=2g00<Y#4R3#4!s$'R4#HR5#DR6/B6R7#@f1R8#8P0f3R99072%>8%=8R:'<%;3%;4'AR4,::'3R:[^07f2R3#91?93#8P2f5R;9072P!sB$%9;A7662R<f7R=555#1X27=67=9072R>!sL%f6R:955<!sC$R?=67:#9g01SKp4p710R@P1\2R1%@3RAP0A69329098f4RB?038P9P3O1#2'3[RCA0982P3P8!s8%A6B9890B3RD[A0;93PBP9!sA%\DP9P3P8P2CGP8n20010!s#$12!s-%0W6X78W5W3PC^6A^78^51^3@P2P7f9R@!u&+P3P@P8O5A073@A7663f8!uc$#2'3P0f:9079A7669=55@#1#2%>B%=BRB'<1:B4'3P2f<RB907!vN$:=55B#1#2P@P=P8O2W:W1P8P2O2!tu7b1b4X1>X07AC?:2CE1?:;#8eW9W8!s\6!s/&W4X;6W<o"). Qed.

Lemma maps_subtract_In : ltac2:(zQ "c1!htf!ig4!ij9!il4!hk3!is6!ila!isd!re!it4!it9!iu7&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$6~0>2lo$4>2hi$4>1e~0>0@3$3~0^1@3$b^4^3^2@2$9~0\2e0~0@2$8@3$3~0^1^6@3$3~0^3@4$a@3$5@1$1@1$0#k0@1$1@1$0#k0^1@3$7@1$1@1$0#k0@1$1@1$0#k0^1^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##6Ap'0h02e0h13Hinh21eh32hih42loh54mapsh61Hh72H0h82H1h92IHh:1ah;2a0h<1lh=2szi001bi011pi021xp;1p;2p;3p;4p;5g007_j17Tg00HFj1ITg018^j1BTg01?RR0j2?Tg00Clj1HTg01VYj34Tg01A8j30Tg005dj39Tg01>4j38Tg01WUR1j25!s^$Lj1>Tg00c?j33Tg01:Aj46!sL$oj4=Tg01Xij5GTg01D^R2j2FTg00K9j3;Tg007Ej2DTg01Cjj3CTg01Q1j4<Tg01YGj4:!s^$Dj3ATg01E8j5ETg00ADR3j2@Tf5R4f4R5f3R6f2R7f1R8f0R9C=30p=1A0678/@9p=2g00<Y#7!s$-I#BR:/?:R;#HR<P;g00SjR=A467890;9P;P9P4P;P7A9::9R>A8::9R?P5P6E1R@C2X0;,5;[^2;^3=]4RAX5<%>;RB?4!si%g00mh!sn$BP;P6P>P?P4P5E1!sb'P9n010!s#%W1X2;X3=X4=P0P:P:A3;45!sq'P;P9f7R0f6RB53;P!tM3^4=\A^<<P9P:P:PBP4C6=3;!sf/0PBP6P7C=R@A4467RCP8P9DGA0;8@A0;8C'FP2P;P7f8R2P0!u_%A4B5690;7!u>$:P:f:R7f9RCC6R@=3;2RDP;P5!uR$BP4!uR/!uj$CP2!uj%P;!sh+;REP7!tn$CP;P4!sb$0PBE1RF!sd$P@A0;@!s~$A9::@A8::@!t+%A;;@!sD$21D;@3CP9C<C:W1P9O1A404590;6!ua$4P5P9O4!tC$CPF!te+!tW'7P;PB!tI$2P0!u,&!tp+=RBf<R1!tr$E!vZ$>P?PCP2!uV29!su$2!sD$7PCE1C2P3A0;8BP;PCA9::8A8::8PEP7!uy$!t,%AR7f@RCC6f?R353;P;PE!v`&1!t0/A0;63P;P1A9::5A8::5f>R5PB!vm0DfCR1C6fBR6!sr%!wT%CP3!uM'4!y'$1P6C6R6=3;790;4P;PBA9::4A8::4P3P5!v}$64A0;47;A8!vz&8W7P8P9O2n20!zl%1012!zu&W6X0;!sE7102000b0!wa%!sB-211000!s'$b1!{[-X9AX5<X=:X::!sw-101!sw'0100X;;P9DEW5o"). Qed.

Lemma iv_subtract_contains : ltac2:(zQ "h01!htf!ig4!s4!iia!hk3!ij9!re!hne!m5!it4!im2!it9!ht8!hs9!il4!ma&@2$5@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>2sz@1$1@1$0#k0>2lo$4>2hi$4>1x$4>1y$4>0@2$8^4^3>0@2$2@2$3@1$0#k0^7^3>0@2$8^4^3>0@2$2^4@2$7@2$3@1$0#k0^9@2$3@1$0#k0^8>0@2$2@2$7@2$3@1$0#k0^a@2$3@1$0#k0^9@2$f+2+k0>0@2$a@2$2^6^9@2$2^8^7@2$9~0\1e~0@2$6@3$e~0^1@4$b^d^c^b^a@2$6@2$2@1$d^1^9@2$2^8@1$c^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##lch02H1h14__x1h24__x2h34__x3h44__x4h54__x5h64__p1h76__sat3h84__x6h9!s6%2h:7__arithh;4__ffh<8__varmaph=5__with>1eh?4__p2h@2z1hA1xhB2HdhC1mhD1nhE1zhF2HahG!s}%1hH1bhI1yhJ1HhK2H0hL3HaxhM3HlhhN3HwfhO3HxyhP2HyhQ1ahR2hihS2lohT2szp%0p&0p;1p;2p;3p;4p;6p;5p;<p;Bp;7p;8g007_j1PTg00HFk10^Tg018^k10FTg009dR0j22Tg01:aj21Tg00@hj20Tg00XZj2:Tg008Dj1r!sU$GR1j2\Tg01D^R2j2DTg01Yak20<Tg01ZTk10]Tg01?Rk20VTg00Clj1~Tg01JNj29Tg00W_j24Tg01[=j2TTg01=Nj25!sS$Lj1x!sA$Zj2RTg01<Mj1hTg01>Qj1iTg00ADR3j2;Tg01WUj2YTg01\7k20?!s0$WR4j1lTg007Ej2NTg00K9j3CTg01]5j3y!s/$[k109Tg01^9k406!s0$\k60!v%$_Ek40!uy$A_k20XTg00BGk30W!s0$kk20UTg00]ej1GTg00^Dj2}Tg00DLj2_Tg00c_k10S!s9$jk10RTg00EHk10Q!vo$bj1fTg00Gdk10!tr$FVj2{Tg00Ikk20MTg00JMk20L!u7$Sk30ETg00L2k40!w<$2gj4u!x#$Aj4c!tB$?j3@Tg01A8j3ETg01Cjj3d!uH$lj5sTg01`Jk20CTg00`?k10B!s0$]k20ATg00a>j3jTg00fhj3^!te$3j2m!yT$dk30=!si$lj2`Tg005Fj6e!s/$dj3q!wj$4j3kTg01Q1j4v!y2$Gj4t!tb$Ok601!yP$Dk30!x,$b7k20G!x7$ok40KTg01FZk308!sD$Ym<07Tg01c>mB0O!s0$dm<0!{4$jUj3g!u&$gj2!w^$d=k40T!vt$9j4!vV$Ldj7!zC$IGj8[Tg014jk60[Tg00MHk70!zE$EZk70Z!um$Ek30YTf2R5f1R6f0R7':'0p=>g00S0R8/07p==1267,;5p=If5R9f4R:f3R;P5P6Cc;@7p=HB085679E:;p=F1056/;7p=7g00VBR<g00VbR=7C7p=]g00SjR>/N7p=Ug01dIR?P>!s$$4P4P9P:P!t%$P7N<07p>05!sD&!s$%1P7P6P5P1P;P:P9f6R1f7R4f8R@f9RANB0Op>0\!sR$0P4P0P1!sz2Pp>031}>7p=JAg>67p=6g00THR0g00m<RB,W6!uM$|P>!s\%H0Tp=31{>7p=SP>P6g00U[RCP7CLp=MP5g00MlRDg00NKREPEg00NkRFP>P6P!sL$g00OKRCFVp=ZP9PDPEPEPFP:!s0+>P;g00U4RGP5CLPCFVP6P7G[p=<!sL-;!s0+5!sI/zAC>!wi&?!s1$p=bAg>56/WB=@07p=BP6!sa+7J0[p=p!u>&k>RH!u>%Q!t,0!sV-PCFVK04p=8P5!s<+6P7K0Zp=X!s:->P6PGP7!u6%p=AB0Y!t[$K!s@,p=o!t52!u8$aP1!s;+!wu%!sI2G[p=O10!u\&n1W7Bp>0@A@067p>0>!tT2H!tT+>0:!u+34p=w!xh$/WBp>0H!sk$9@05p>0I1W5B1W6!vV$5@0p>0Jg00<YRB#PRD#PRC#P!s$%RH$0^RG$0FRI12;5S0011G1/05Q!s0$@RJ11G45>;11GA/:J%rDRJ%rHRH'\RK'0109@1041'Df;RL-0<GRM11GLRN#=&0]G7INRNPMPNP210@Lf:R2/0A20VIIRNPNP7PNP<%~NRMf?RO,1GRPf=RQ'9RRPNPIPIPOf>RS,1GRT14QP'T,5G%xNRUEHPUn010!s#$20000P<PMf<RV1:PTRW'9S01!sj%1RPVRX,5G14WX,5GP!sc6DF%h7RX%i7RW,0277L';X>N'YP510AVP<PRP=P31967#]1256S02[1267R31956#][RYQ0219;5#][20?67P7n20!t3'1!t4$000XC>XD>S03PY^C>^D>S04P7f@RY,1GRZPS%=PR[%lGR\,\JR],2PR^';AI[PKR_P[P^P[P7XA>R^PHO1R`,\JRa,2Pp-0Rb/N[ACb[[e9y[[P^&093XI>XA>R3PPPP%UPP]PaP^!s$$>P>g01dg1\67H06#U!tj%PJPJ%UJP\P`P^P^%l7#UXA?PGPH%UHJ05N:0\R?L03J02P;H00R`P_fAR\,1GR[#=Rc12[]Rd';AIc[KRePcPdPc12[a1NbcACbcce9yccP^P3P[P[%U[!te$!sz'9H00R?Pe20XJHRa128JR]%=H128K[R3[R^%=JRcg00SNRdB0WJH6UWFRH%=K\d^FcRc!~w$:@20U8J'NP]eO1R]P3g00l]Rd#GRf#GRg#GRh#JS05%JgRg%Jf1}>dRd'6S06'6'6Rf%x0Ri'|S07%~0R01_>;S08&0S>Rj7351_>:Rk?3:j736&0R>Rl&0Q>RmPm%fD#SRn%SDRD&0NEREPmPm%SCRC/MnP!s4$1{>BRoPCPEAZmoDE<DzE<20MmFRFP7P51N<=20L75#]dB0E>86H0DRpb;b<b=X1>X2>X3>X4>10;612;:Rq105:Pq[[[^1>^2>^3>^4>P7P\fBS09fDRqfFRr,1GS0:P4PSPOO7b:b9bGb9b0b0O3b0CuAC<=RP<P=!}Z'PMP6!|\%Q09Q09,1GRR,4YRs,T[Rt!|d&S0;!}L71:R[Ru,9O!}F'RORv!}F$uv!s`+<!}I510QW97XSS0=!}D$,YNXH<P!#3?&!ss$P\14O[,TZ!so+>!tA%[ZRu,9S!tA'[SRw!tA%w,5GS0?!sS%@!tD7VW97XQS0A!tD$!t4$Y14SZ,TPS0B!se$CCcRuPNPuPNA@NuUS0D!tE%ZPS0E,9QS0F!tG%ZQRP!sY$GQ0E/4PS0H!s5$ICcRx=@NUS0J!tS3RyDF%hu%iu,0L77VS0KPNQ0DPyPuQ0D9ENuAENuyACNu!s0$U1NNu3d3dDsP>Q0BA>V[797[QXE>P`P_P!|\$C[sS0L12[s??t[1bts97s['DS0MfCRs!y'$N,4\,TRS0OP>PaP^PHPcP]P3&0BB-0A>S0P%GhRh#JRt5j>RyQ05/6dS0Q16gdS0R=Byi3BP0A3k5j1_>9Ry1_>1Rg73;736S0SPl!{b$pm@S0TPm%fBRB#f#SRz,QCC8!sA$AS0UPmA^>no!s;$5XmPEPm%SBR{=AmnS0V!|Q%P{1KozPEPmAAmoDS0WPEPmQ0WPm1KoC,o{C8CaE<FOPFP!|H6X5>X8>X6bX?bA?1;914:79?4;'D10;9S0XA>:5410;:10:9S0Y1::47n1[!|r2^5>^8>^6b^?bP7fH,1GR|,4rR}fG,1GR~'012~}S0ZP~PrP:PsPqP|P9PAPOP\O<b:b7b9b7b@b0b0b0Q0C,1GQ0B!x-'Q0LQ0MQ!w_3Q!wW$S0O!#4{$R}5j>S0M!s:$L#JRh16td,6}S0CQ0C!sh%#J!wy$O'6S0M$0@S0[00>i'|3B7BfP0Q08?35yA3k1g736!ww%Q0TPm1QozC8S0C!wc$DCS0\=AmzPmQ0\,Qo!wo+Pm1m>8R8!sC%1m>J>0=>GRJ,MzC8!sH%%PB#SRBPD!x+$ZmnBS0\!x8&Cn!s/&8oPm1MoJC8S0]FO!x7FA?179S0^1465S0_Q0_,b7779'D%=1?I1KS0_101;12141014%=9?I9K[!x?<P7Q!w{$!ww%rP:P9P4PAPY!w}7'`EeAqIIu,1GRrAk!s0%9>Lr77VeQ0KeCvCt19ZSRZP7J01b0WBP7O110L2P<Q01P=Q03Q04P7PQQ0E!xm'!xb17P0A3j5yRrA3k;j!wk+PoP!#9R%PB1KD{Rj!{u%\!#9Y$jCaE<E<!v`<107;A>95;12911::9,2;!v55P7P\Q09fERj!za$:PsP4PQPSO8!#9A4Q019C<=!#9C019RYQ!#8{8P6Q!#8Z6Q!#8R8!sr$[OQ0>!sY3Q0@DFQ!#7j&xP!s&%<PMPZQ0D!sT3RZQ0JDF%hx%ix!#6s$R[PNPZQ0JPxAENxZQ0J9ENxACNx!s7$U1NNx3d40;DsP>PPQ0?!xX$V7977QXE>P>Q0HA>Vw797w!#700GRORw12RO??vO1bvR97OR'DRRQ0N/RYRv!~B36Q0Q=Bti5BtP0Q!#6B$!~,$UB0:moCRZ5wm!}2&AAmzD!#5t+CnR=!s4&C!|z%Q0W!}u$=o,Ko,o{C8E<!#5xHQ0^A?47;'D1015A>:91101:Q0Y1:4@/4:,::!#5rC10j|R=12|jPjP~P|!|g$:!#5`>I!y}$H!{q+wPRP!vA4[20H}fQ05Q0R'6,6tQ0M=Bhi5B}40IP0A3k;g93r!|8&AZmonPm1Q{nC8!#54'{!#4q-Q0UPm1MDJ!#4`&PnPB!s0&z1KoDR!w,&1MBz!s>&o!sH%A^>D{RD9Am8!si'!#Cd$!w-I127;??5;A?157'DAI@5K1091A>@;:12@ARD109A1:14/4@Rn#=?In!#4q$!w?>%=~P=!w4$jP:!w@$!#4w$OPYP\O>!#4y6Q0G,1G!w?AOQ0P=j>h16}d'6R}Q0L#G#J/6}16tf=Bhi40J5Bh!#9N%1yA3k5!#9N+AZmC{Pm1Qo{C8Q0T=wmZ!wI+AAm8CPm1MC!wK&Q!#>7$1KCzRz=AmJ!w>&BPz!#5@'Q0]!#>1$!w1DQ02??76A?175'D%=;?I;KQ0X1:9@/0KA>@1AQ0_\D!#8l>P=!#8k'j!{-$1PAPSPOPYO=!vr3,`P!#8n$x,1GRPAk!s0%9>LP77VeP[eCvCtQ0F!#8j/!#PW'10211000!s'$!#5Y-TV!#G5%S11GQRQ14VT'T!#RK9!sY$:TQRQ,9L!#GG&TLRT,5G14Q!s];DF10AW97X2!#70&ebKbJPVPLP2PAH0K9EN7104W97X@!sJ+WBWNWPWOWLWM!#QC$XR>XS>XTIWQo"). Qed.

Lemma maps_subtract_In_intro : ltac2:(zQ "a1!htf!ig4!ij9!il4!hk3!is6!ila!isd!it9!iu7&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$6~0>2lo$4>2hi$4>1e~0>2e'~0>0@3$3~0^2^5>0@3$3~0^2@4$8@3$5@1$1@1$0#k0@1$1@1$0#k0^3@3$7@1$1@1$0#k0@1$1@1$0#k0^3^5^4@3$3~0^3@3$9^7^6^5").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##1Tp'0h01eh12H'h22e'h32hih42loh53Hinh64mapsh71Hh82IHh91ah:2a0h;1lh<2szi001bi011pp;1p;2p;3p;4p;7p;5g007_j13Tg00HFj1DTg018^j1=Tg01?RR0j2<Tg00Clj1CTg01A8j30Tg005dj37Tg01>4j36Tg01Woj42!sS$Lj1;Tg00c?j34Tg01:Aj45Tg01VYj3:Tg00K9j39Tg01D^R1j28Tg01Cjj3B!t3$Oj7A!sC$Dj3?Tg01_lj5>Tg01E8j5@Tf4R2f3R3f2R4f1R5f0R63:30p=1g00<Y#3!s$-D#=R7/<7R8#CR9P8g00SjR:A0852A7774A6774P2P3C29085R;P8P4f6R<f5R=P2D1[[^28^08^3:]4R>X69%;8R?9085g00mhP8P3P?P<P=D1P5n010!s#%X1;W5X28X08X3:X4:P0P7P7A48<=9085!t6$8R0f7R?548P!t;$\;!t<,^4:\>^;9P6P7P7P?P<C5=48!sc&f9R@P0P=P2C2A:?=2P4P1!sO$@P0C5R1=983A083?f:RAP@P<P=!uY$3!u#$0!u#%'8P5!s[$AP@C5=982P8P7P7f;R3PAC5RBA7776A6776P0P?!sh$=f=f<RC!t7$2908<P8P<P3P@P0D1'8]1X08A777BA677B!u/$29082PC!tG$!sk&P8P=PAP0P?D1;B6W1P=P6P4FAW7P6O1A0820P3PA!sf-8P2P@P?P<D1P0!w:%P2P6P4O63?W5P6O1n20!wH'2110!s3&D>P8P4A481?!w-%e!wd4X8>X69X<7X97P5P6O2!sq$10!s$$!sr$100X:8P6D@W6o"). Qed.

Lemma wcov_mono : ltac2:(zQ "72!htf!ig4!ij9!ila!hk3!iv7!il4&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>4maps~1>5maps'~1>2lo$4>2hi$4>0>1e~0>0@3$6~0^1^5@3$6~0^2^5>0@3$5^5^3^2@3$5^5^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##-Dp'0h01eh11Hh22Hch32Heh42Hrh52Hsh62Hxh72hih82loh94mapsh:5maps'h;1xi001xp;1p;2p;3p;4g007_j13Tg00HFj1?Tg018^j19Tg01?Rj28Tg00Clj1>Tg01A8j30Tg01eKj37Tg01<Mj15Tg01>Qj14Tg00ADR0j22Tg01WUR1j26Tg01Q1j4:Tg01YGj4=Tg00@hj2<Tg009dj2;Tf3R2f2R3'<f1R4f0R5';'2p=1g00<Y#3!s$-?#9R6/86R6#>R7g00SjR8f4R99065A0649[^06A7934P9P5P5P2C1P3P4P5O2f8R:9065%55R;P3P3%45R<C1'2X06,66P1P6f9R19065R=P;P2P2P!sF'P;P9P9P<C1,2=!sV&5f;R=9065P;f5R>P>!sT%P0f<R09064%54f6R?P?%44C1f!sR&P:P:P!tF/5f>9062%59P1P1%49C1P6f@!sT&=P=!tT,>f?906>%5>f:R<P<%4>C1P0P>P4O2P5C:C=W4W!ug&n20010!s#$12!s-%0W1X06!sE61!s0%b0W6X;8A7923eW2W5X78W8X:7W9o"). Qed.

(* [comment removed for export] *)
Lemma live_bytes_cons : ltac2:(zQ "b1!htf!ig4!ij9!ivf!iq7!ila!ii2!hi5!hk3!hne!iia&@2$2@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1l@1$5~0@3$7$8@1$3@3$4~0@4$6@1$1@1$0#k0@1$1@1$0#k0^3^2^1@2$9@2$a@1$0#k0^2@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01ah11lh21np;1p;2g007_j10Tg00HFj18Tg018^j12Tg01?Rj21Tg00Clj17Tg01:aj26Tg01fMj13Tg00XZj24Tg007Ej25Tg00<Y#0#0#0#0#0#0#8R0#2R11111#7g00Sjf1,60f0#3'4'5W1X21W0o"). Qed.
Lemma live_bytes_app : ltac2:(zQ "92!htf!ig4!ij9!ivf!ila!ip8!hi5!hk3!hne&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2l1~1>2l2~1@3$6$7@1$3@3$5~0^2^1@2$8@1$3^2@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "p'0h02l2h12l1h21zh34__x1h44__x2h54__x3h62IHh77__arithh84__ffh98__varmaph:5__with;1ah<2a0h=1lh>1ni001bi011pp;1p;2p;3p;4p;7p;6p;5g007_j13Tg00HFj1NTg018^j1GTg01?RR0j2ATg00Clj1<Tg01FZj34Tg01fMj11Tg00XZj20Tg00CLj1;Tg007Ej29Tg00c?j36Tg01:aj2:Tg01:Aj4@Tg00DLj2?Tg00d=j4MTg00Djj1LTg00EHj1KTg00FVj27Tg008bj1JTg00fEj35Tg00G9j4ITg00Ldj7FTg00Ikj2ETg00JMj2DTg00K9j3>Tg00KSj3CTg00L2j4HTg005Fj68Tg01gFj3=Tg01E8j5BTg00SjR1f1R2f0R33>p=2g00<YR4#3R5#3#3#3#3#3#NR6#GR7/A7R8#<R9P8A4823#1%12R:%13R;'0'2^09R<X19%;8#1/0;,91X09P0P7P7f3R0f2R=568R>=483#1%1>/0;'2^09\<^=9P3P11:60R>A48=3R?#1R@'0P7P7f5f4RAC@=680#1/0:,23X21P1%1=RB,0>1:6AR6A4802#1'0103:'2X21P110B;1063%10RB,06/0:'2X21g00THR>#;%<>P11?1=P21?10CM%L1%K1R>g00Mlg00NKRCPCg00NkRCP11714RD1715R5%J4,71R4551551g00k>A51D5=514CIg00OKFF1E>CP3P=g00VBRCg00VbR>'91D3==>C>dg00S0=C12CHb8b9b:X31X41X51102=,031032/0='2^31^41^51P3P:PBP6O3b7P@P2P3O1E8P7P7PAP0C@R@=68=R6#1RBA=A0=E8A68@?#1A=A0?E8A4863#110B;'2eX09X6<X19X>7X;7P2P3O2n2001101010121100100X<8P3DBW1o"). Qed.
Lemma live_bytes_nonneg : ltac2:(zQ "60!htf!ig4!ila!ij9!ivf!s4>1l@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0@2$5Z@1$4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "p'0h01lh14__p1h24__x1h34__x2h41Hh52IHh67__arithh74__ffh88__varmaph95__with:1ah;2a0h<1nh=1zi001bi011pp;1p;2p;3p;4p;6p;7p;5p;8g007_j10Tg00HFj1`Tg018^j1MTg01?RR0j2DTg00Clj1@Tg01fMj11Tg01hTj3LTg00CLj18Tg01iIj4ETg00c?j36Tg01:aj27Tg00XZj2?Tg01Yaj2_Tg01ZTj1VTg009dj2>Tg00ADj2<Tg00]ej1=Tg00^Dj23Tg00jUj3;Tg00agj2RTg00DLj2QTg00c_j1KTg00d=j4ITg00Djj1HTg00EHj1FTg00F3j2GTg00FVj29Tg014jj6JTg00MHj7CTg00Gdj1NTg00fEj3OTg00Ikj2BTg007Ej2PTg00JMj2ATg00K9j3STg00KSj3TTg00L2j4^Tg01:Aj4]Tg01gFj3\Tg005Fj6WTg01E8j5XTg00@hR1j2YTg00G9j4UTg00Ldj7ZTg00IGj8[Tg00S0R2f0R3'Yp=2g00SjR4f1R5g00U4P3CUp=5P5g00MlR6g00NKR7P7g00NkR8P3g00OKFZp=4f3R9P6P7P7P8f2R:P5P3G[p=:g00<YR;#0R<#0#0#0#0#0#`R=#MR>/D>R?#@R@P?%13#2RAX0@P4P1g01j79L41%8?#1CEP0P>P>A6?:5#1#2\A^0@P3P417=:R0%15'?%23R1X=41_=:%20%V=RB,>0'<p-0R0g00THRCg00l]RD#=RE#=,34134E134D5;45;4g00m<'R%8C36%@CP41Q4:P5%K4CI%H4%F4RCPCP6P7P7P81G42RD194;R;'5,4CPCP6P7P7P8f4R6EJFC%N7R7PC194<R<,5D,4CP7AO4;<,5D,4CC:C:1BC8P3P:g00VBRCg00VbR8'P1A3:=SC8dAT425C^b7b8b9X24X34W11<1:%2:1?:9#2[[^24^34^10P317=6R6/>B%19P6P5P:O5b6b4P>P>P9P:C]=6?5#1A\9:5EWX5AX0@X<>X:>P5P3O2n2001101000121100100X;?P3DXW0o"). Qed.

(* [comment removed for export] *)
Lemma map_remove_notin : ltac2:(zQ "92!htf!ig4!ij9!ila!hi5!is6!jgc!ir9!il4&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>4maps~1>1b@1$1@1$0#k0>0>1e~0>0@3$8~0^1^3@1$6@3$4@1$1@1$0#k0@3$5@1$1@1$0#k0@1$1@1$0#k0^2^3@3$4~1@2$7^3^2^3").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##3rp'0h01bi001bh11Eh21ah31eh41li011lh54mapsh61Hh71pi021ph82H0h92Heh:2IHh;2a0h<2b0h=1ni032Ini042l'p;1p;2p;3p;4p;8p;5g007_j14Tg00HFj1ITg018^j1@Tg01?RR0j2=Tg00ClR1j1HTg01A8j32Tg005dj3:Tg00K9j30Tg00[2j1>Tg01Sgj28!s^$Lj1<Tg007Ej26Tg00c?j33j2?Tg01:Aj47Tg01T`j31Tg01H0j15Tg01QLj3;Tg01j\j3GTg01D^j2CTg01Cjj3B!tX$kj2A!sA$Dj3DTg01kQj8ETg01E8j5FTg00VBR2f0R3g00VbR430p=9g00<Y#4!s$-IR5#@R6/=6R7#HR8P7f2R99273f1R:9:66=069#>R;[^37189:=089[^06R<X58%<7R=9273P!sF%68=W6X06P0P6P6f4R0f3R=537R>!sL-8>:=08>[^06\<^48P3!sT$5R>P0C7=37=R?!sU,A15>:P21623f6R;=159=023P2f8R@=150!s4%P8%5:!sn$9RAP@C7RBA:663RC=15;#5X77f7RD5;7RE537PEn010!s#$20000A37BD508]1P:A15D=RB#9!s|%4P6P6P@PDC7R4A15C>!st$=;7;RC537REPC!ss44;RF508g00ADA15:3#9A069:[RGA06:3A159:#9RH[A06=9\HAG5:3P:n20!sq'1!sr$000X06X26PG^06^26P3PAP>P:O3A06A>P>!uk$:PAC7RAA07AAp-0RG^48^27P1P7PGP3g00mhA07:=P0P=P3O2'Cn1011!t;$20020100104X48X27p?1001103PAP@O2167A3BP3O3b1b8'AW1g01KlR=902BP8P81?74R4P4PCP;P8\8/64P>P0A273DP>P:A07A:A27:@;D3O2W9X37O2GE!w#%=P!v`4=08FeW1n0110001!tm$1P3O1b1b<18?:=08?e!z&$X:<X58X=!vB$:P3O2!vb$!sZ&21!uN$0X;7P3DFW5o"). Qed.

Lemma map_remove_split : ltac2:(zQ "d2!htf!ig4!ij9!ila!ip8!ii2!hi5!it4!iq7!re!ir9!ipf!il4&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0>4maps~1>1b@1$1@1$0#k0>1n@1$1@1$0#k0>0@1$b^3>0@3$c~0@4$5@1$1@1$0#k0@1$1@1$0#k0^3^2^4@2$7~1\2l1~1@2$7~1\2l2~1@2$9@3$6~1^7@3$4~0^2@3$8~0@4$5@1$1@1$0#k0@1$1@1$0#k0^6^5^1@3$6~1@2$a^7^6@3$4~0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##wfp'0h02l2h12l1h21ei001eh31Hh42e'h52H1h61Eh71bi011bh82H0h92Hbh:2Hph;1Dh<2Heh=2Weh>3Hinh?1ah@1li021lhA1nhB2H2hC4__p1hD4__p2hE4__p3hF6__sat4hG4__x1hH4__x2hI4__x3hJ4mapshK2EehL2IHhM3WF'hN2H3hO2HahP2WFhQ2WbhR7__arithhS4__ffhT!t$%3hU8__varmaphV5__withW2e0hX2ebhY1pi031phZ2szh[2H4h\4Hin'h]2Hrh^2a0h_2b0h`2eni041xp%0p&0p;1p;2p;4p;3p;6p;9p;:p;5p;=p;7p;8g007_j1HTg00HFk103Tg018^j1oTg01?RR0j2gTg00ClR1j1cTg01MZj1BTg01:Aj40Tg01A8j34Tg01FZj36Tg01WUS00j23!sa$Lj1ZTg00c?j32Tg01>Qj1ATg008Dj1aTg009Gj2zTg01@2R2j1:Tg00K9R3j31!t/$Oj6m!s/$kj2_Tg01BJj28Tg01CMj6TTg01DDj3UTg01Q1j4WTg007Ej2=Tg01H0j1LTg01Sgj2ETg005dj3\!se$jj3VTg00A_j2f!tY$dj2JTg00@hj2<Tg00BGj3e!s/$kk202Tg00DLj2dTg00d=k401!s9$jk100Tg00EHj1~Tg00FVj2Y!u^$bj1{Tg00fEj3bTg00G9j4S!s/$dj1yTg00Ikj2xTg00JMj2w!uw$Sj3sTg00L2j4rTg00XZj2>!uc$^R4j2^!wL$aj2I!uJ$Fl9]j6Gl:[l=uTg00[2j1qTg01knj3pTg01T`j3DTg01m=j2nTg01YGj4PTg01j\j3tTg01_lj5lTg01E8j5v!v:$DS01j2NTg01<Mj1k!tc$dj7jTg014jj6iTg00MHj7|!s_$Zj7}!uJ$Gj8hTf4R5f3R6f2R7f1R8f0R93236p=;f6R:f5R;;151E78=169'Np=?P5P6P7P8C0=2;9p=7%k6/J71<8!sF$@!sS'p=9f7R<A267896;571:/N9p=51E56A678951;p=C!s1$9156p=KP8g00MlR=g00NKR>P>g00NkR?P9g00OKFjp=RP8P=P>P>P?P9Eip=XP7!s7+8P9F|p=Q!s92}p=`P6!s9+7P8P9Ghp=Fg00VB!t=$VbR@719p=M1J78!tx$Og00<YS02#HS03#H!s$'RA$03RB#oRC/gCRD#cREPD%B7PCPC!v9%RF=4D6PEP:PDP8PD!s@$;P5C0RGP9D;S04!sC$;A6D89RHF?X0E,3EX1E,3E[[^AC^7CRIXJE%ZDRJ#BA4DFJg00mhRKPEPJ!s~-:P;C0RLP9D;RM!sB$:P!sx2P9n010000100W>WPXACX7CP0PCPCA2D56RN#BA2D;5RO94DFPEf8RP=2D<RQQ!tz$QP;P!tu:\I^@EP9A2DG6!sl$L594DFQ01!to&PP<P:E794D9P8%A8RLPLQ03#aRL%aARA'zRGC@RQ[^2D!sY&<P:P;E7#:PE!s8%f:RRf9RSPPE7RTPMPEPT!u^68A4D9TP!sq$%:TP2!sd&=S05f<R2f;RTE7RM91E8!t%+@RUf?RVf>S06E7RW!vz-2PTC0RXP9PEPWP2PHC9G5!t@/RW[P9!sQ$TPRC0S07=2DSS0891EJA2DXRS0991EJ!w_$1PDp-!sv$g00SNRYPKn1011020002!s%$!s#$X2Eg01F>PMP9EmPK1_W9b8W3P9O1W3A4D98RW1868RM[^4D%:8RZA2D67!uH&CR[fBS0:fAS0;E751!ua'DR\P[Q0:E791ENPEPEP1PDPEP9P;P9!tZ2103102XWEPO!se&ES0<P\P[E7P9ETA1E5[!vd$1PDPDP9P<P8!sj;A2D:;!sk$FS0=Q0<C0R1=2D\P8ETA1D:1!sC$GR1Q0=C091D<!vw%fHROP1!s8$P!tU&IS0>POC0A1ESORN!xb%!v$&TPE!sJ$ORMfNR]C0R^fMR_52DR`!xG,fKRafJRbC0S0?!xL$`Pa!xL5]8]3[XYDA1EP1P9PNPEQ0>!x]$]P_C0RN/88\W^4D!tD&PRWPMC0S0@=2D]!t@0LRcPaC0S0A!t>&c!t>5^8Z]3X@EA4D9b!t5$_PcC0RZ/88!uU%bA4D9cR`!{I'aQ0<P8A1D^8A4D8_;U9O2X<`X2DP9CW%BaP4!so$bQ0>C0R491DNA4D4c!u$&QR4PWC0R`=2DMRd!u#&Z!tr$dP_!tr5P1Q0?91D^P3PDQ0@A1D8N!ss&UR3fTRdC0S0BfSRe52DRf!sy&`!#5O$CPEPfP4!}p3[P9Q0@Q0A51DA1D`Z!vT$0!u1$CP9P9n2001103000120!y{$1X2!vy%RR`P4C0S0DPN!zW%C4_!sg28!sg>PeP`C0P^!zI%CeMA1CdWP9A1C34S0EPCP`fVRf=1C`Rg!#3>&P6fYRhfXRiE7Rj!xX,PfP3C0Rk!va$jPf!va5[X7CQ0EP9Pg!tK$!}T'WRgP7Ph!su2gPfC0S0F!sv&g!sv5X7CPCPd!sV&8PhP!ta$94D9!y>'j!sA$7fZRjC0Q0F51Df[Rl94D9Rm!sB$;f]RnC0!z$&!x?%PlPjC0S0G=2DnRo!tc%Q0G!tY$oPl!|@65]6]:]9X?C!t]&3PiPgE7Ro!t]/o!vG&hC0=1DkA4D9!tp%hf\Rk!tT,CPgA4D9k!t[&7C0Ro!sB,CPjP8C!xR%jPhC0Rp51DA2Don#:!tM&nP5f_Ro!#9u%!tM$!uR&of^RqC0RrfaRs52DRt!w;&r!uU$tPo!uU69]:]6]5XZC18p8\m!tW'hPiC0Rm=1DmA2Dpk#:!s=$kPl!s=$2DqRt!tP0!tR%qPnC0S0Hf`Ru52DRv!w%'H!tR$vPq!tR2PJ!sb+nPkC0S0I=2Do!s_$JPDQ0I!s_&n!s7$9EC!sc$PqA6DJtRv91Et!uS$kA6DJqS0JC91=EvP=P@PEP=PE%L9Q0I1EonRn52DPn!#>y%!#:<%!s}$oDKX7=A4D9oA\CC8RJ=1CqS0KP:P7P8O218r7P5P6!tw$uPoC0S0L=1D6fbRn94D6;U7O2P6%A6RvPvPGC@RvP;!sU$sPuC0RtA1DttfcRw94Dt1=Dt3VO2Pt%AtRxPxPGC@!~<%feR094D9fdRx91CJ!sj$0PxC0RJ/87PK^=v];]K]<!t-&8P9C0fhRv54DA\CCFfgRy51!#3/$vPyC0Rz!~>%P7C0'8!s2$5P6C0R{%A{R{P{!tL$CfjR{!#3d%;C0fmS0M5!x}%flR|fkR}!zZ&8P:!so+7P<C0R~%A~R~P~!so$K]=];]<XX!tQ%{P5C0=4D|!s4$}P{C0S0N!s3&;!so+|P:!so21fLAS0Og00S0R~/JLS0P1<~A1J~G[S0Q[S0R1<~LS0SAeLA8VYWOS0TQ0S1<~G\Y]OS0SP8g00:@202~L'=Q0PeO1S0PQ0Qg00SjRLg00THRY#ZS0U%cYS0VPL1dL7P81dL6H01S0W&00LS0X%~LRYPLQ02,YLRAg00U[S0YQ02#{,YL9bLAS02CS,RYS0Z1XY;S0[5QY%y>R>P!s`%g00U4S02PA!sN&\PLQ03!se+3Q!sB-25`YP!s`$PAQ0YQ03!s?&31XY:S0Y5QYP>1XY<S0]CFCFCF1xY?S0^P9P71==@1w97#MdAsL~8CrS0_bSbUbVXGLXHLWIXCXXDXXEX1>97=O961>86S0`/<81>87/<8'^1>76R~=O7:PP[[[^GL^HL^IL^CX^DX^EXP9PKfq,IBR?1IBTS0a'>/<Gfp,IBRA,>?/<GPAQ0aP?PVP;P5O9bRbFbTbFPKePKeW=W;W<P;P7P6P8P9M9]!s9$KW<X`CXX!{J$O2!#;8/1!#;8$!#N}&O4bQb=b;WKQ0K#qeW<X2D9pqk!~a%@R@1EqkRq92DmPq!~a1Q0J51EeADBkk1nBkEGCWCPCPW9W:W6W5PlP;P9P8P7P6M:[W5W6W:W9PiP6P]P_PPP2M:[PgP9EGb[WNPf!s0$NW8P9O1b!s+&!#Fl&n2002!u<%010101A1D9Z!#5Z%dPeC0Rl=2D`Rk!#6:&@P9PEPkPW!#H}5k[XYDQ0AO1P91=DZO1b3W6P9O1Q0?=4D_P_PcPaP7P9O4PEP!#J'&N!#Iy%]!sz5Q00PEPEP4!sQ&^!sQ$4PM!sQ2P!#>P$eQ0CPEPe!#A:-!si'dPDP7PDQ0D!#B^%`!s7$!#7l'!uk%iPgC0Re=2DfRkA2Dl9Rl96D8!uk$d!#Ob4PEPfA6D5lPEPfPdA6D59F?Q01PEPgPDP;Q0B=2D8DK!s7$3PDP;P8ECPEA2DmjR3!uO&e!sq$3Pi!uz5!s@$hPDP<Q0F=2D6!sr$DPP!s]$5D;A2Dr7Re!#>B-eA4Dm6A4D9!#7>$wPnC0Rm!#Fi';%B:PEP<PuPDPUP2EC!uv&yffReC0Ri=2DR!tl+m!tl&w!tl5[]M]B]5]>]:]9^LIXJEPDPRPDPpP:D;Rp#BPDPT!#@i$<D;R<!#Rc$PDQ06!#<|$RD;RF!#Ri$F!#Ri<Q0H=2DpRp!u^/pQ0G=4D<PDQ05!#=9$S!t2&!#PH$nPsC0Rp!uo+<%B!tK$PVPDPrPTD;Po!s4$T!uy$!u{%eP0C0RoPDQ0:PDPpQ06D;52DRr!v-&p!v-$rPn!zE3CPCPxPwC0Rr=2DURp!sz$DQ0;PDPtQ05D;92DJRF!s:$!s1$JPDPt!sv$FPs!#??02Q0L=2D2RJ96DU92DrRrA6DpJRJ51E!tP$u!t\$2EC1=EJADBxuP=1==9ADB0s=1=9P=ADByw!s1$!#?j%8A6D\p/ExRp92DzPp!#?l2A2Dz\RpPUDK]6P8ADBenRn#MP=PEP@PDP[!y&$VD;/EwRw92DiRmPw!sm1A2Di[R@=6DVRs51EQ01ADB89#MA1C78[RuA1C89ADB78#MRJ[A1C67\JAtB8!#Jq&!su%1!#Ti'7CX?CPu^7C^?CP9PvPxP8O3A1CvxPCP0A6D1@R@!xl+7P}!#Fn+!#I8&{P@E7!#FB'6P|PDQ0>!s5%fiR@PvC0R0Q0<D;!#FX/K]9]:]5X?CPDQ0=PDPoQ0:D;!#HL%!|L$P{!t>3eP@Po!t>-vP}A6DOpRv!t'0DPOPpPzA4DzOA4DzpA1Dz!s5$\1=Dz3V3UDlA4DzvP6P0P9O2!st$@P|C0/80P!#^_${P@C0R!#AO${Q0MC0=1D0PDPbPDP0Q0=D;94D0;U8O2P0%A0R0P0PGC@!#D|%}fnC0R}A1D}}PDPaPDQ0NP1!s\$}1=D}3VO2P}%A}R}P}PGC@Q0OQ0RQ0TQ0SQ0PQ0QQ0UQ0VQ0WQ0XPYQ03Q0[5QYP>PYQ0ZQ!#>f%PYQ02Q0\5`YP>Q!#>o&Q0^Q!#>U0XIL!#>V-8=O96Q0`=O8;1<~71>75/<7'^!#>M>o,IBRX,>A/<Gfs,IBRB!s3%PXPBPAP5P;P:!#>F2!#=Y$b\W9W:W5P@P9PPPRPTM9]b6b3'_W6g01KlRP91=nPEA6D[VR[A2Dz9A6D\U92Dz51EX@E!{p$,=EPwP6EG!}:%PP!|?4=1EseW6n0110101020101P9O1b6b_!#>D%]WMWBW5W>W:W9WLPjP9PhP`P4P2PUPVQ06M=uW3!#@2,!#=q%2!t8&W3X0E!sE7104!sE%1!sE,1!sE3b2W>P9O1!sa-2!sK$!s'$b!tj$PRP9EGbBW8PS!s0$!#?T%b!s+&W5P9P7P8O3W5W8W3X@EX2D!#Ap$P9O4n02!#]z$!uy%411!s0%!s#$Q0991E9!#U}'VQ06Q05E7RV!#@0&7P9PEPVPT!#Ur6@EQ08O1P9Q09,=E!t^$:W9!vN>!#fP'XLIXJEXZCX?!#D221!#D2+X^DP9DvWJo"). Qed.

Lemma live_bytes_remove : ltac2:(zQ "h11!htf!ig4!ij9!jh2!hi5!ivf!ir9!ila!jhc!ii2!re!jj5!hk3!ipf!il4!jjc!iia&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$7~0>1b@1$1@1$0#k0>1n@1$1@1$0#k0>0@1$d^3>0@3$e~0@4$9@1$1@1$0#k0@1$1@1$0#k0^3^2^4@2$a@3$4$c@1$5@2$6^5^4@2$f@1$5^5@2$h0@1$0#k0^3@3$4$8@2$3~0@2$6^5^4@2$b@2$3~0^5N1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##L0p'0h02l2h11nh21Hh31zh41lh52l1h64__p1h74__x1h84__x2h94__x3h:4__x4h;4__x5h<4__x6h=1xi001xh>1Eh?2H3h@3HinhA2HrhB2WFhC7__arithhD4__ffhE8__varmaphF5__withG1bhH4cstrhI5cstr0hJ1ehK1mhL4mapshM1yhN2z3p&0p;1p;2p;4p;3p;5p;6p;<p;7p;Bp;8g007_j1ATg00HFk10<Tg018^j1wTg01?Rj2lTg00Clj1fTg01MZk105Tg01:Aj4JTg01A8j3vTg01nDj5tTg01Sgj2:Tg01FZj3?Tg00K9j34j1ZTg00ADR0j23Tg01WUR1j2OTg01fMj11!s~$aj2>Tg00W_j2!t8$oSj20Tg00]eR2j1HTg0203j2;Tg007Ej2E!tU$Oj6PTg00XZR3j22!sL$Jj2Q!s/$aR4j19Tg008Dj1kTg01[Zj2MTg01][j1jTg021Aj2i!s/$dj3hTg01cdm<09Tg01^\k608Tg022Aj1eTg00@hj2BTg01b7k206Tg009dj2dTg01D^j2bTg00^Dj2LTg00jUj3KTg00agj2YTg00`?k104!s0$]k203!sC$>k302!w9$Lk101Tg00c?j3ITg00DLj2XTg00d=j4R!sA$_k10!v:$Djj1~Tg00EHj1}Tg014jj6|!uh$bj1^Tg00FVj2F!s/$3j2\Tg00fhj3]Tg01EZj7uTg00Gdj1xTg00Ikj2sTg00JMj2y!x3$Sj3zTg00L2j4r!v%$fj4{Tg023Qj3_Tg005Fj6GTg01gFj3qTg0240j2`!vj$>lBa!vM$Yl<p!tL$Ej3o!tC$9j4c!t$$dj7nTg00MHk707!tV$Gj8mTf5R5f4R6f3R7f2R8f1R9CJf0R:3Ip=<A?89:9467p=6g025=R;?49:p=7g00SjR<?489/3:p=8A4<9:p=@AI89:9?67p=W1289/5:p=D159:94<8p=[A4;9:,38p=SP;!s$$<P<P<g025\P4!s$$3g026<P5P6P7P8P9P:MBap=g!sT+2!sM$7g026_!sG&<pp>0;!sx27C!sx%f6R2g027c!sz3>0:Ao!u/$CP<P9g00k>P:Ccp=N!s4$MlR3g00NKR=P=g00NkR>P:g00OKFnp==P8P3P=P=P>P9P:K07p=V!so&U4!so%UP7!sJ+!tF$Gmp=Tg00<YR?#AR@#ARA#!s$&$0<RB#wRC/lCRD#fRE&058PCPCP8P9CJ=vD7!u8,DtPEP2PDP9PD!sJ$5P6P:E<D61:25RFA?D9:RG54E'3X0E,OEX5E,OEP1PEPEf7RH!sb-2P5!sb'H2=4EG!sZ-%1F%121>B6'510DF10D2g00l]RF#HRI';'738P:PEf9RJ!sz,f8RKPH!s|'JK!s|/!tR&:R1PDP8!tR&JPK!sT%PE1:1JRG!sB$:D6!s\$%1G%111>BK!tT$G10D1RG/;I!tL+<RLPDP6!tL&;RMP1!sv,LM!sB$!st$P0PEf=R0PDP5!tJ&LPMP9!sR'0L!s@$9D6f>RN/:0RO#1%1N1>BL!tK$O10DNRO!tK/?RPPDPH!su&NP0P7!su%f@RN/:PPDPKP6D6PEA?DJ5%1:RQfBRR#1RS1>BN!s~$:RT10DRRU!t$&X4EPEfARV1@QSX4E%1VRQ,E<PDPJ!t8+PCJP5DWRPP9EP%1P/@QP<PDP1!sH&VPNCJP2DWR1#1A?DMHRQ#1RP1>BVRW,5:10DQRQfCRX,0DRY!tJ'3<PEPR17TYX4E1E;UP1P8EP10D1/7UP;!t,&RPVPHE<RU9?DMR1,0DRTA?DLKRZ#1PDPL!sN&XPRCJPKDWRX#11>BRR['5R\10DZRZ1;:IR]!tE$1;P<%1MR^%1HR_'2R`10DX/;IRX,7ZRZ98:\X3<P<%1UR\,2^%1LRa%1KRb'2Rc15:[;8Z!sH$12W_R_ADa:[=8c!s:$;10DMRZ10DHRd'QRe12[b,2a=[c[Rc?S:XX1;!sL$U,QZRX10DLRL10DK'Q=Sc]X1;12^_=[`WR`%HdRW,QZR_/;IR^,7eRc'3%9ZR]%9dR['2Rbg00S0Rf%k?Rg,2[Rh,2]Ri/5g'MRj'@Rk,3`P`PcP`Pk%j`P;P<%Z;P4%Z<%99%9:'@179:1i9:3hXM;X=;PePbPZP]1E<]RbPdP[1E<[R;EgP^Pj159:,MfXK<X1<P_PiPZP]PbPWPh12:gX=<PdP[P;H0;EgPIPg1E<gK0:N<09J08%ed1Bf[%eL%9LRL,Bf10D0#910DJ#9/2g;DgRJ-06f1dfJ1MfJR0/@J'31BJfA4<0f'3'b%9O%9G!sT%,MfP<p-0RGg00THRO%HIR0#HRJ,L<R[1L<01L<I1L<FRF5K<!s%%g00m<R0'Y%HJ,L<&04?-03<>02<[=K!sQ&/Y01YF0&01O5IO5IO3I%fOP<P<1X<6P81X<2CRP9!s6$5P7&00<CRCR%~<%}<ROPO!#7C'!s0,KE|%^?R3#A,F<RF1F<ARA%^@,F<R01\<gR['C'C=]<[R['N,=O5VO1\<fRJ,U[,=O1NFJ!s<%Fu%x=R=PO1UJA,=OP!s1%0!s1$1F<?R?1F<@R@'C1F<3R3/C@,C?=]<3!t#$1CA0/NF!ss%CTCTCT1sO>P:P8g00VBROg00VbR>'E1y:8=4O>dAz<f9CrbDbEbFX7<X8<X9<X:<X;<X<<W6126g=D7gR>,@5,321B>fA4<5!x#$1Bf61Bf212761256=D75122H/@K38[[[^7<^8<^9<^:<^;<^<<^6GP:10DN#9RG12L!xa$dfP9PLPGfF,>BPa%1NP8P7P6O:bCbNb?bIbHC{1;XI9S`eePTA_DMUEGPQA_DMHEGP\AqRVHEG%111`!sA$P1`!s@$YP:EPb2PS!s-%1:VNP:EGWAW>P9P:O2n20010!s#$12!s/&W2X0E!sE71!sE'5!sE,1!sE3bJW@WBX1CXGCWLo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lbrk_bytes : ltac2:(zQ "20!hk3!jk2>1L$1$0") := ltac2:(zQ "93!hk3!ij9!jka!jl4!jm1!jme!jk2!jn8!jne&M1\1p@2$1$0$0$0^1\1z$0\1l$0^1&\1p@2$1$0$0~0&M2\1x@1$2@2$1$0$0$0@1$3^1~1Z\1L$6M4\1x$4$0@1$5^1~2\3cur$0M2\1x@1$2@2$1$0$0$0@1$3^2~1Z\3cur$0@2$8+2$7~2~2").
Definition lbrk_cnt : ltac2:(zQ "20!hk3!jk2>1L$1$0") := ltac2:(zQ "a4!hk3!ij9!jka!jl4!jn8!jo4!jjc!jm1!jme!jk2&\1z$0\1l$0@2$6@2$5^1$4+1&M1\1p@2$1$0$0$0^1~0&\1p@2$1$0$0~1&M2\1x@1$2@2$1$0$0$0@1$3^1~2Z\1L$9M7\1x$7$0@1$8^1~3\3cur$0M2\1x@1$2@2$1$0$0$0@1$3^2~2Z\3cur$0+1~3~3").

Definition sum_glen : ltac2:(zQ "30!hk3!ila!ij9>1l@1$1@2$2$0$0$0") := ltac2:(zQ "70!hk3!ij9!ila!isd!hn3!joa!hne\1l@1$2@2$1$0$0@5$5$0@2$1$0$0\1g@2$1$0$0\3acc$0@2$6@1$4@3$3$0$0^2^1Z^1").
Definition sum_mlen : ltac2:(zQ "30!hk3!ij9!ila>1l@1$2@2$1@2$1$0$0$0$0") := ltac2:(zQ "80!hk3!ij9!is6!ila!isd!hn3!joa!hne\1l@1$3@2$1@2$1$0$0$0@5$6$0@2$1@2$1$0$0$0\1m@2$1@2$1$0$0$0\3acc$0@2$7@1$5@3$4$0$0@3$2@2$1$0$0$0^2^1Z^1").

(* [comment removed for export] *)
Definition ltotal : ltac2:(zQ "20!hk3!jk2>1L$1$0") := ltac2:(zQ "70!hne!jp8!jq5!jk2!jue!jvc!kg8\1L$3@2$0@2$0@1$5@1$1^1@1$6@1$2^1@1$4^1").
Definition lcount : ltac2:(zQ "20!hk3!jk2>1L$1$0") := ltac2:(zQ "90!hk3!ij9!jh2!hne!kh4!jp8!jq5!jk2!khd\1L$7@2$3@2$3@1$4@2$2@2$1$0$0@1$5^1@1$4@2$2@2$1@2$1$0$0$0@1$6^1@1$8^1").

Arguments sum_glen l : simpl never.
Arguments sum_mlen l : simpl never.
Lemma sum_glen_cons : ltac2:(zQ "90!hk3!ij9!jvc!iq7!ila!ii2!hi5!hn3!hne>1b$0>1l$0>2gs@1$4@2$1$0$0@3$6$0@1$2@3$3@2$1$0$0@4$5$0$0^3^2^1@2$8@1$7^2@1$2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01bh12gsh21lp;2p;1g01?Rj25Tg00Clj14Tg013Cj10Tg028Jj11Tg00XZj23Tg007Ej22Tg00SjR01500#4f1#0f0#1'3,20W1X20W0o"). Qed.
Lemma sum_mlen_cons : ltac2:(zQ "90!hk3!ij9!ii2!kg8!iq7!ila!hi5!hn3!hne>1b$0>1l$0>1k$0>2ms@1$5@2$1@2$1$0$0$0@3$6$0@1$3@3$4@2$1@2$1$0$0$0@4$2@2$1$0$0$0@4$2$0$0^4^3^2^1@2$8@1$7^3@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01bh11kh21lh32msp;2p;1g01?Rj20Tg00Clj15Tg013Cj12Tg029Qj11Tg00XZj24Tg007Ej23Tg00SjR01000/00#5f2#2f0#1'4,30W3X10X20W0o"). Qed.
Lemma sum_glen_app : ltac2:(zQ "70!hk3!ij9!jvc!ila!ip8!hi5!hne>2l1@1$3@2$1$0$0>2l2@1$3@2$1$0$0@3$5$0@1$2@3$4@2$1$0$0^2^1@2$6@1$2^2@1$2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "p'0h02l2h12l1h21zi001zh34__x1h44__x2h54__x3h61lh72IHh87__arithh94__ffh:8__varmaph;5__with<1ah=1bi011pp;2p;1p;3p;4p;7p;6p;5g01?RR0j2LTg00Clj1?Tg01FZj33Tg028Jj11Tg00XZj20Tg00CLj1;Tg007Ej2=Tg00c?j35Tg013Cj1>Tg01:Aj48Tg00DLj29Tg00d=j4@Tg00Djj1KTg00EHj1JTg00FVj27Tg007_j1ITg008bj1HTg00fEj34Tg00G9j4GTg00Ldj7FTg00Ikj2ETg00JMj2DTg00K9j3:Tg00KSj3CTg00L2j4BTg005Fj66Tg02:Xj3<Tg01E8j5ATg00SjR1f1R2f0R33:p=21L11R4#?R5P4A3423#1%12R6%13R7'0'2^05R8X15%;4#1/07,=1X05P0P1P1f3R0f2R9554R:=343#1%1:/07'2^05\8^65P3P1%>0R:A3493R;#1R<'0P1P1f5f4R=C8=540#1/06,23X21P1%19R>,0:%>=R:A3402#1'01036'2X21P110>710:3%10R>,0:/06'2X21g00THR?#;%??P11919P21910C@%K1%J1R?g00Mlg00NKR@P@g00NkR@P1g00<YRA,71RB%IA,71RC%HA,71RA541541g00k>A41BC=41ACGg00OKFF1E?@P3P9g00VBR@g00VbR?'=1D39=:@?dg00S0=C12CBb9b:b;X31X41X511029,031032/09'2^31^41^51P3P6P>P:O3b8P<P2P3O1E6P1P1P=P0C8R<=549R:#1R>A<=09E6A54<;#1A<=0;E6A34:3#110>7'2eX05X78X15X61X=1P2P3O2n2001101000121100100X<4P3DAW1o"). Qed.
Lemma sum_mlen_bump : ltac2:(zQ "70!hk3!ij9!kg8!ila!hi5!kk0!kk7>1a$0>2ms@1$3@2$1@2$1$0$0$0@3$4$0@1$2@4$5@2$1@2$1$0$0$0@2$1@2$1$0$0$0@1$6^2^1@1$2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) [] "##1/p'0h01zi001zh11lh22msh32IHh41ah52a0h61bi011bh72b0h81kh91pi021pp;2p;1p;3p;6p;4p;5g01?RR0j2<Tg00Clj1FTg029Qj10!s8$Lj1ETg007Ej2;Tg00c?j33Tg008Dj1ATg00XZj21Tg00YTj2@Tg02;dj2?Tg013Cj1>Tg005Fj66Tg02<Aj47Tg01E8j5DTg02=Mj1CTg02>Tj4BTg00K9j3=Tg01:Aj4:Tf3R1f2R2f1R3#Cf0R4CBp=2g00SjR5%03;=4p=4P2P5P3P4C:p=5P5!s3,9A=534p=81<55R6/<5R7#FR8P7!s$$2P4C2%04R9'4X28%E7#0,;5P0P6P5P7P7f4R:P4C2/49!s5$5R;A3723R<C2%0<'4[^18P4P0!tC$7P7f8!sU/9A5612=373R0C2%00!sW%^05P4!sG$;!sT&g00<Y#AR9/12g00oP'@,1:f<R0'?g00VBR<P<P<P7P4f6/9;R<11:9556A56<:R<n010!s#$20000!t%$>P1C2R=537A37<1#0R<'4P4P5%>:R>!sI$=P2C2R?#0R@'1RA184<X05R<P5%02RB,1>R>%>;RC%0='1/84X05P5PB11C4%01,1C'8X051;5>P@P3E619;:R@=561R>=372#0P;P:P1P2C7E6RC1119R9956@=37?!sD&9P?C7E6P5PAP<PCA37>!sA'1!sA%n011!uW$!uT$b!x&%019:1=56!v}%2C2%02'4eW3X28X85X15X6!xv$O2n20011!sd$121100100X96!sC92100X57P4DDW2X45o"). Qed.
Lemma length_bump : ltac2:(zQ "80!hk3!ij9!jh2!ila!jhc!hi5!kk0!kk7>1a$0>2ms@1$3@2$1@2$1$0$0$0@3$5$4@2$2@2$1@2$1$0$0$0@4$6@2$1@2$1$0$0$0@2$1@2$1$0$0$0@1$7^2^1@2$2@2$1@2$1$0$0$0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) [] "h01ah12msp;2p;1p;4g01?Rj20Tg00Clj13Tg02=Mj12Tg02?0j41Tg00SjR01000/00R0#3P0P0f1#2f0C1W1W0o"). Qed.

Definition BUDCAP : ltac2:(zQ "10!hk3$0") := ltac2:(zQ "10!ma@2$0+2+i2").     (* [comment removed for export] *)

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

(* [comment removed for export] *)
Record KLB (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKLB {
  kb_minv : mminv mo;
  kb_halt : m_halted mo = None;
  kb_wf : vmwf (vm_maps (m_vmmaps mo));
  kb_nawf : forall e, In e (vm_noaccess (m_vmmaps mo)) -> ehi e <= 2^64;
  (* 75d69e00: [State.init_reserved] makes the reserved ledger the image's
     reservations FOLLOWED BY the launch's vDSO/vvar pair, so the old equality
     is false at the launch -- [ld_resv] holds the image's entries only.  The
     ledger is now a PREFIX of [vm_reserved]; the tail is bounded by
     [kb_resv_top] and [kb_vdso_in] below.
     SHAPE from a donor tree
     projects/boost-beast/http_request/proofs/lib/Spec/KLink.v:356-357. *)
  kb_resv : exists lo hi, vm_reserved (m_vmmaps mo) = lo ++ hi
      /\ ld_resv L = rband (alloc_top (m_vmmaps mo)) :: map wwZ lo;
  kb_top : CEIL_MIN <= alloc_top (m_vmmaps mo) <= CEIL_MAX;
  kb_hceil : alloc_top (m_vmmaps mo) = hceil;
  (* Same cause: the pair sits inside the mmap window, not below the break, so
     the one-sided bound is false at the launch.  Weakened to openssl/pem's
     shape (its Spec/KInv.v:211-213 [kl_resv_top]): every entry
     is below the break or one of at most two small entries.  Chosen over
     boost-beast's two-sided form BECAUSE THE LAUNCH CAN PROVE IT WITHOUT A NEW
     PREMISE -- the witness needs only [State.vdso_len_bounds], while placing
     the pair ABOVE the brk guard would need [valid_mmap_base], which this
     tree's [KM_init] (and the [KINIT_HS] interface statement above it) does
     not carry. *)
  kb_resv_top : exists V, (length V <= 2)%nat /\ live_bytes V <= 20 * 4096 /\
      (forall e, In e (vm_reserved (m_vmmaps mo)) ->
         ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)) \/ In e V);
  kb_resv_wf : forall e, In e (vm_reserved (m_vmmaps mo)) -> elo e < ehi e /\ ehi e - elo e <= 2^34;
  kb_resv_n : (length (vm_reserved (m_vmmaps mo)) <= 8)%nat;
  kb_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_top (m_vmmaps mo);
  kb_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_top (m_vmmaps mo)
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kb_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_top (m_vmmaps mo)
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kb_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kb_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_top (m_vmmaps mo)
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kb_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo)
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  kb_live : vm_live_bytes (m_vmmaps mo) = ltotal L;
  kb_count : Z.of_nat (length (vm_maps (m_vmmaps mo))) = lcount L;
  kb_limit : BUDCAP <= vm_limit (m_vmmaps mo);
  (* 75d69e00's [State.init_reserved] appends the launch's vDSO/vvar pair to the
     reserved ledger ([State.vm_reserved_init_model], State.v:7702-7721, :7844),
     and [MmNodes.mmsafe]'s NMprotect case now demands that the range miss that
     pair (Sys/Mm/Mprotect.v answers [unmodeled] otherwise).  Two fields carry
     that, and both are facts every grant already checks:
       [kb_vdso_in]   the pair is IN the reserved ledger -- true at the launch by
                      [vm_reserved_init_model], and no step rewrites
                      [vm_reserved], [m_kernel], [vm_mmap_base] or [vm_init_sp];
       [kb_vdso_disj] no tracked mapping meets any reserved entry -- true at the
                      launch ([vm_maps] is empty) and preserved because every
                      grant tests [region_free] over [vm_reserved ++ vm_maps].
     Together they put a range lying inside a tracked mapping apart from the
     pair, which is exactly what the NMprotect node now asks for.
     SHAPE taken from openssl/pem's [Spec/KInv.v] [kl_vdso] (lines 199-214)
     and its [Lib/Nodes.v] [minv]'s last conjunct; pem keeps the inclusion in
     [minv], which in this tree is an encoded definition another lane owns, so
     both live here. *)
  kb_vdso_in : incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)))
                    (vm_reserved (m_vmmaps mo));
  kb_vdso_disj : forall r, In r (vm_reserved (m_vmmaps mo)) ->
      forall e, In e (vm_maps (m_vmmaps mo)) -> edisj e r;
  (* LPS 727298f3 port: the launch's channel reader ([State.init_model] seeds it from
     [in_channel_reader], [Run.valid_input] pins that true, no step writes it), which a
     write to stdout/stderr now needs (else SIGPIPE) *)
  kb_rdr : m_channel_reader mo = true }.

Ltac kb_open K :=
  pose proof (kb_minv _ _ _ K) as Kminv; pose proof (kb_halt _ _ _ K) as Khalt; pose proof (kb_wf _ _ _ K) as Kwf; pose proof (kb_nawf _ _ _ K) as Knwf;
  pose proof (kb_resv _ _ _ K) as Kresv; pose proof (kb_top _ _ _ K) as Ktop; pose proof (kb_hceil _ _ _ K) as Khc; pose proof (kb_resv_top _ _ _ K) as Krtop; pose proof (kb_resv_wf _ _ _ K) as Krwf; pose proof (kb_resv_n _ _ _ K) as Krn;
  pose proof (kb_start _ _ _ K) as Kstart;
  pose proof (kb_groups _ _ _ K) as Kgrp; pose proof (kb_metas _ _ _ K) as Kmet; pose proof (kb_distinct _ _ _ K) as Kdis;
  pose proof (kb_brkreg _ _ _ K) as Kbreg; pose proof (kb_phase _ _ _ K) as Kph;
  pose proof (kb_live _ _ _ K) as Klive; pose proof (kb_count _ _ _ K) as Kcnt; pose proof (kb_limit _ _ _ K) as Klim;
  pose proof (kb_vdso_in _ _ _ K) as Kvdi; pose proof (kb_vdso_disj _ _ _ K) as Kvdd;
  pose proof (kb_rdr _ _ _ K) as Krdr.

(* ---- carrying the two vDSO fields across a step ----
   [vdso_top h] is [page_round_down_Z (mmap_top h)] and [mmap_top h] is
   [Z.min (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (alloc_top h))]
   (75d69e00 State.v:3483, :3466), so it reads exactly two ledger fields. *)
Lemma kb_vdso_top_eq : forall h h',
  vm_mmap_base h' = vm_mmap_base h -> alloc_top h' = alloc_top h ->
  vdso_top h' = vdso_top h.
Proof. intros h h' E1 E2. unfold vdso_top, mmap_top. rewrite E1, E2. reflexivity. Qed.

Lemma kb_vdso_in_eq : forall mo mo',
  m_kernel mo' = m_kernel mo ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
  incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)) ->
  incl (vdso_reserved (m_kernel mo') (vdso_top (m_vmmaps mo'))) (vm_reserved (m_vmmaps mo')).
Proof.
  intros mo mo' Ek Er Eb Et H. rewrite Ek, Er, (kb_vdso_top_eq _ _ Eb Et). exact H.
Qed.

(* The disjointness survives any step whose tracked mappings are old ones. *)
Lemma kb_vdso_disj_sub : forall (R R' M M' : list (word * word)),
  (forall r, In r R' -> In r R) ->
  (forall e, In e M' -> In e M) ->
  (forall r, In r R -> forall e, In e M -> edisj e r) ->
  forall r, In r R' -> forall e, In e M' -> edisj e r.
Proof. intros R R' M M' Hr' Hs H r Hr e He. exact (H r (Hr' r Hr) e (Hs e He)). Qed.

(* and a grant adds one mapping, which the grant's own [region_free] over
   [vm_reserved ++ vm_maps] has already put apart from every reserved entry. *)
Lemma kb_vdso_disj_cons : forall (R M : list (word * word)) aw nw,
  region_free (R ++ M) aw nw = true ->
  (forall r, In r R -> forall e, In e M -> edisj e r) ->
  forall r, In r R -> forall e, In e ((aw, nw) :: M) -> edisj e r.
Proof.
  intros R M aw nw Hrf H r Hr e [<-|He]; [|exact (H r Hr e He)].
  destruct r as [rb rs]. unfold edisj, elo, ehi. cbn [fst snd].
  exact (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl Hr))).
Qed.

Lemma map_remove_In : forall maps (a : word) e, In e (map_remove maps a) -> In e maps.
Proof. intros maps a e H. unfold map_remove in H. apply filter_In in H as [H _]. exact H. Qed.

(* [comment removed for export] *)
(* Restated at the revision: the two vDSO fields read [m_kernel] and
   [vm_mmap_base], so a model equal on [m_vmmaps] alone no longer determines
   them.  The added premise is [m_kernel mo' = m_kernel mo]; every call site
   is a [with_vmmaps]-shaped update, where it is [reflexivity]. *)
Lemma KLB_vm_eq : forall L pbrk mo mo',
  KLB L pbrk mo -> mminv mo' -> m_halted mo' = None ->
  m_kernel mo' = m_kernel mo ->
  m_channel_reader mo' = m_channel_reader mo ->
  m_vmmaps mo' = m_vmmaps mo ->
  KLB L pbrk mo'.
Proof. intros L pbrk mo mo' K MI HH EK ER E. kb_open K; constructor; rewrite ?EK, ?ER, ?E; auto. Qed.

(* Restated at the revision, two premises added for the same reason: this one
   names the ledger field by field, so [vm_mmap_base] has to be named too.
   Statement otherwise from
   a donor tree
   projects/boost-beast/http_request/proofs/lib/Spec/KLink.v, its KLB_vm_eq'. *)
Lemma KLB_vm_eq' : forall L pbrk mo mo',
  KLB L pbrk mo -> mminv mo' -> m_halted mo' = None ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) ->
  vm_noaccess (m_vmmaps mo') = vm_noaccess (m_vmmaps mo) ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
  vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo) ->
  alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  m_kernel mo' = m_kernel mo ->
  m_channel_reader mo' = m_channel_reader mo ->
  KLB L pbrk mo'.
Proof.
  intros L pbrk mo mo' K MI HH H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. kb_open K.
  assert (Hrdr : m_channel_reader mo' = true) by (rewrite H10; exact Krdr).
  assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps mo')) ->
                   forall e, In e (vm_maps (m_vmmaps mo')) -> edisj e r).
  { intros r Hr e He. rewrite H1 in Hr. rewrite H2 in He. exact (Kvdd r Hr e He). }
  constructor;
    try exact (kb_vdso_in_eq mo mo' H9 H1 H8 H7 Kvdi);
    try exact Hvdd; try exact Hrdr;
    unfold vm_live_bytes in *; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?H7; auto.
Qed.

Definition phase_inv : ltac2:(zQ "40!hk3!kl4!jm1!jk2>2ph$2>1L$3>4pbrk$0>2mo$1P") := ltac2:(zQ "i13!hk3!ij9!re!hi5!htf!hne!klc!s4!ig4!jn8!jne!iia!jka!ii2!lg9!jl4!kqe!it4!lk3!jm1!il4!im2!hn3!ll2!lla!kl4!pe!lhd!ht8!hs9!jp8!jq5!jk2&@3$3$0^1@2$b@1$4#k0@1$h2@1$6^2&@3$3@1$c@2$1$0$0@1$f^4@1$h0@2$1$0$0&@2$1@1$8@1$4#k0@1$8@1$4#k0\2ph$h3\1L$i0\4pbrk$0\2mo$h9Mh3\2ph$h3P^4@2$2@3$3@1$8@1$4#k0@1$e@1$6^1@1$h2@1$6^1@3$3@1$c@2$1$0$0@1$f^3@1$h0@2$1$0$0\3cur$0@2$2~0@2$2@3$3$0@2$b@1$4#k0@1$e@1$6^2^1@2$2@3$3$0^3^1~1\3cur$0@2$2~0@2$2@3$3$0@2$b@1$4#k0@1$e@1$6^2@2$5^1@2$a+2$9@2$2@3$3$0^3@2$5^1@2$a+2$9@2$2~1@2$2@2$7@2$5^1@2$a+2$9@1$ha@1$6^2@2$2@2$h1~2\1e~2@2$2@3$h4~2^1@1$hb@1$6^3@2$2@2$7@1$hd^1^2@2$7@2$5^2@2$a+2$9@1$hc^1@2$2>1b$0>1l$0>0@3$h4@2$1$0$0@4$d$0$0^2^1@1$he^6@2$h5@2$7@2$5^3@1$h6^2^4@2$7@2$5^4@2$a+2$9^3>1b$0>1l$0>1k$0>0@3$h4@2$1@2$1$0$0$0@4$d@2$1$0$0$0@4$d$0$0^3^2^1@1$hf^7@2$h5@2$7@2$5^4@1$h6^3^5@2$7@2$5^5@2$a+2$9^4@2$h1$0\1b$0@2$h1$0\1l$0@2$2@3$3@1$c@2$1$0$0@1$f^5@2$h7@2$1$0$0@4$d$0$0^2^1@2$2@3$3$0@2$b@1$4#k0@1$e@1$6^3@2$5^2^1@3$3$0^4@2$5^2^1$h8").

(* [comment removed for export] *)
(* [vm_only] is written out here, and its three laws are explicit tactic proofs.

   OLD (7 conjuncts, decoded from the two zQ strings this hunk replaced; printed by
   [CDef.decode] at image sha256:2c6b6db8):
     fun m m' : Model =>
       m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
       m_tid m' = m_tid m /\ m_stdin m' = m_stdin m /\ m_creds m' = m_creds m /\
       m_net m' = m_net m

   NEW adds [m_channel_reader m' = m_channel_reader m] and NOTHING else: the body stays
   boost-json's.  The conjunct's donor is openssl/pem, which has [vm_only] written out and
   carrying it (projects/openssl/pem/proofs/lib/Lib/Nodes.v:1368-1374); pem's *body* is a
   different shape (it lacks [m_creds] and [m_net], which this tree's consumers use, and
   carries six conjuncts they never establish), so only the conjunct was ported.

   Why: [rz_writev1_wall]/[rz_writev2_wall] gained an [m_channel_reader model = true]
   premise at the revision, and nothing in this tree carried the reader fact down to the
   five Ref callers.  [MPRES_laws] (Ref/HeapSR_iface.v:59, BJ/HeapMF_iface.v:93) asks only
   for reflexivity and transitivity, and the concrete [hs_MPRES] is this [vm_only]
   (Ref/MallocSR.v:87, Ref/MallocMF.v). *)
Definition vm_only (m m' : Model) : Prop :=
  m_fds m' = m_fds m /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\
  m_tid m' = m_tid m /\ m_stdin m' = m_stdin m /\ m_creds m' = m_creds m /\
  m_net m' = m_net m /\ m_channel_reader m' = m_channel_reader m.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros mo. unfold vm_only. repeat split; reflexivity. Qed.

Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
  intros a b c H1 H2. unfold vm_only in H1, H2 |- *.
  destruct H1 as (F1 & S1 & Ha1 & T1 & I1 & C1 & N1 & R1).
  destruct H2 as (F2 & S2 & Ha2 & T2 & I2 & C2 & N2 & R2).
  repeat split; etransitivity; eassumption.
Qed.

Lemma vm_only_with_vmmaps : forall (h : VmMaps) (m : Model), vm_only m (with_vmmaps h m).
Proof. intros h m. unfold vm_only. repeat split; reflexivity. Qed.

Definition frame_ok : ltac2:(zQ "20!kl4!mk5>1G>0$1>0$0PP") := ltac2:(zQ "90!kl4!mk5!hi5!hk3!mkf!ml8!ij9!mm1!lv0\1G>0$1>0$0P>1s$1>2s'$1>2mo$0>3mo'$0>0@3$2@2$6$3$3@1$4^3@1$4^4>0@3$2$7@1$5^4@1$5^5>0@2$8^4^3>0@2^8^7^5@2^9^7^5").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ev_fixed : ltac2:(zQ "20!ina!hk3>5flags$1$0") := ltac2:(zQ "50!mm9!hk3!mn1!mo0!mo6\5flags$1@1$0@2$3@2$4^1$2Z").

(* [comment removed for export] *)
Definition ev_costb : ltac2:(zQ "20!hk3!mod>1e$1$0") := ltac2:(zQ "a0!hk3!ina!mod!hn3!mp1!jn8!mpd!mq3!mo0!jne\1e$2M2\1e$2$0^1\3req$0M1\0$1$0@2$8^1ZZ@2$9+2$5\4addr$0\3len$0\4prot$0\5flags$0M1\0$1$0@1$4^1Z@1$3^3\4addr$0\3len$0Z\4addr$0\3len$0\4prot$0Z\1p$6\5caddr$0\4hint$0Z\3why$7Z").
Definition ev_costk : ltac2:(zQ "20!hk3!mod>1e$1$0") := ltac2:(zQ "70!hk3!ina!mod!mp1!mpd!mq3!mo0\1e$2M2\1e$2$0^1\3req$0M1\0$1$0@2$6^1ZZ+1\4addr$0\3len$0\4prot$0\5flags$0M1\0$1$0@1$3^1Z+1\4addr$0\3len$0Z\4addr$0\3len$0\4prot$0Z\1p$4\5caddr$0\4hint$0Z\3why$5Z").
(* [comment removed for export] *)
Definition ans_cont : ltac2:(zQ "20!hk3!mod>1e$1>1z$0P") := ltac2:(zQ "b0!hk3!ina!lla!mod!mr1!hi5!mr9!mp1!mpd!ms2!mq3\1e$3\1z$0M3\1e$3P^2\4addr$0$2\4addr$0\3len$0\4prot$0\5flags$0M1\0$1P@1$7^1$2@3$5$1@1$9^5$6\4addr$0\3len$0$2\4addr$0\3len$0\4prot$0@3$5$0^4Z\1p$8\5caddr$0\4hint$0$4\3why$a$4").

(* [comment removed for export] *)
Fixpoint tbound {R} (t : stree ev Z R) (cb ck : Z) (P : R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => ev_costb e <= cb /\ ev_costk e <= ck /\
               forall z, ans_cont e z -> tbound (k z) (cb - ev_costb e) (ck - ev_costk e) P
  end.


(* [comment removed for export] *)
Definition RESV_MAX : Z := 8.
Definition BUD : ltac2:(zQ "30!hk3!kl4!jk2>1L$2>2mo$1>2cb$0>2ck$0P") := ltac2:(zQ "e0!re!s4!hne!hk3!msa!kl4!klc!lh2!nh3!jk2!nhd!ni9!nj3!m5\1L$9\2mo$5\2cb$3\2ck$3@2$0@2$1Z^2@2$0@2$1Z^1@2$0@2$1@2$2@1$c^4^2$4@2$0@2$1$4@1$7@1$6^3@2$d@2$2@2$2@1$b^4^1$a$8").

Lemma BUD_mono : ltac2:(zQ "60!hk3!s4!re!njd!kl4!jk2>1L$5>2mo$4>2cb$0>2ck$0>3cb'$0>3ck'$0>0@4$3^6^5^4^3>0@2$2@2$1Z^3@2$1^3^5>0@2$2@2$1Z^3@2$1^3^5@4$3^9^8^5^4").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##;_h01Hh14__x1h25__x10h34__x2h44__x3h54__x4h64__x5h74__x6h84__x7h94__x8h:4__x9h;2B0h<2B1h=2B2h>2B3h?2B4h@2HbhA2HkhB1LhC7__arithhD4__ffhE8__varmaphF5__withG2cbhH3cb'hI2ckhJ3ck'hK2mop;4p;1p;2p;3p;7p;8g03=6j4;Tg02f7j19Tg00XZj20Tg00ADR0j22Tg00@hj21Tg00]ej1@Tg00^Dj2BTg00jUj3DTg00agj2MTg00CLj1`Tg00c?j3K!s8$lj1[Tg00DLj2F!sA$_j1Y!s8$jj1XTg00EHj1WTg00F3j2VTg007_j1CTg008bj1ETg00Gdj1U!sJ$Vj2I!s8$9j4GTg00Ikj2Q!s\$Ej2PTg00JMj2RTg00K9j3O!s/$Sj3STg00L2j4TTg009dj2HTg02hCj1NTg02C2j1LTg02jOj1JTg00d=j4_!s\$dj7^Tg00MHj7]Tg00fEj3\!tL$Gj8ZTg00S0R1f0R2'1p=3g031SR3,12p=:%L2#J,13p=7f1R4#N/02g03>8R5'0g03??R6'Hp=6f2R71242'2p=?g00SjR8P7P4P2C_p==1I82p=4P8P4g00U4P2CGp=!s4%MlR9g00NKR:P:g00NkR;P2g00OKF^p=5P7P9P:P:P;P4P2F]p=>A\842p=<f3R<!sC+!t<$GZp=A!u+$p=ag02lJg02mNf5R9f4R=P<P7C;P0%3=%3<R>f6R?#9/0=#:%7916?<'23?11<9,2>R>f9R@f8RAP9P=C;\>[P2%3?R>%9@f7RB'0#:%7A16@?'25?>P0%3BRCf:RD#9/0A#:%7@16DB3?11B@,2CRCf=REf<RFP@PAC;\C!sy$@%9Ef;RC!sw%F16ED3?P0f>RG#9/0F#:%7E16GC'2%3C11CE'2RHfARIf@RJPEPFC;\H[P2%9J/0G#:%7J16IG'2P0%7IfBR0f?RG'6%3G11GI'2RGfERHfDREPIPJC;\G[P2fCRG#716H0%30110E'2R0g00THRJg00l]RI#@RK#@#@RL#@RM#@#@,B81B8L1B8IRI5D85D8g00m<RL'M1B8M1B8K=D8I5D8/ML%`J5KJ3K%[J1F8A%Y8RJ7==1F8D?=?J7=71F8@?=9J1F8B7=<7=4%X8%W8RJ1V81RLg00<YRI#CRK#4RM'8,5JRN%EKRO#C#4RP,8M,5J5>J%U:R:PJ1I8IRQ,8L,5JRL%CKRK#E#4RR,8Q!sO%P:PJP8%EIRI!si$S/<P%EI#4RP'<g00U[RT%CK#4RUCG,5!sV$%4KRK%4O!tN%O!s9%IRI/<R/8K!sK$1<IQ!s2&81<SM/<PPTP!si%9>JO5>J9>JN9>JLCA!s$'1QJ;P2P7g00VB!w=$VbR;'P1R27=OJ;dAS814CTbDbEbFX18X38X48X58X68X78X88X98X:8X28%34114@'2R110BC/0A/H@11?B10?F/1B%3910B9/1A11A@10D?/0C/HF3?7?>[[[\1[^18^38^48^58^68^78^88^98^:8^28P2fFfGR1P6P5fIR5#NfHR6#aP3%95PEPHP4P7P<P=PAO?bCP6P1PEPGC;eXA0W@W?W>P4P2O2n20010!s#$12!s/&W0W=!sD@<!sD@;!sD?XJ8XH8XI8XG8WKWBo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_maps_next_noop : ltac2:(zQ "90!htf!ig4!ila!ij9!hi5!s9!lg9!lhd!nn8>1h$5>3req@1$1@1$0#k0@3$4@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0@3$8^2^1@1$6^2@1$7^2").
Proof.
  intros h req. unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

Lemma brk_unmaps_noop : ltac2:(zQ "71!htf!ig4!ij9!ila!no9!hi5!np0&@2$2@1$1@1$0#k0@1$1@1$0#k0>1r@1$1@1$0#k0@3$5@1$3~0@2$6^1^1@1$4~0").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##'rp'0h01bi001bh11rp;1p;2p;4p;3p;6g007_j10Tg00HFj1ATg018^j1;Tg01?Rj26Tg00Clj1@Tg01:aj25Tg01JNj21Tg00iWj14Tg01=Nj23Tg00W_j2:!sS$Aj47!se$Lj18Tg00c?j39Tg00K9j32Tg007Ej2?Tg03CDj1>Tg005Fj6<Tg03Djj2=Tg00<Y#0!s$-AR0#;R1g00VBR2g01Kl1611R3#@R4P2P4g00S0R5f1,50R6'1P2P4f0R7P1P1%46R6,301:66,30C7%83R6593P6n010!s#$20000!s63;26X021507R0,15P2!s$$4P7P6!sQ3=246P71?46R2P2n011!sB,b0%40R0/10%>0E<1=77=246eW1o"). Qed.

Lemma brk_model_next_noop : ltac2:(zQ "h02!htf!ig4!hi5!re!ila!ij9!lg9!hk3!s9!pe!lh2!lhd!li7!lj5!lk3!npe&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>1h$8>3req@1$1@1$0#k0=2h'$8@3$f^2^1@1$6^2@2$3@3$2~1@1$d^1@1$d^3@2$3@3$2~1@1$b^1@1$b^3@2$3@3$2~1@1$c^1@1$c^3@2$3@3$2@1$1@1$0#k0@1$e^1@1$e^3@2$3@3$2@1$1@1$0#k0@1$6^1@1$6^3@2$3@3$2$7@1$a^1@1$a^3@3$2$7@1$9^1@1$9^3").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["HC"] "h01lh11hh22h'h33reqp;1p;2p;3p;4p;6g007_j16Tg00HFj1JTg018^j1FTg01?Rj2CTg00Clj1ITg02G9j1=Tg02M=j18Tg00K9j30Tg02I5j1>Tg02W<j1;Tg03Djj2@Tg03Eij29Tg02ROj1:Tg02jOj1?Tg03G2j3BTg00@0j17Tg00ADj21Tg00CLj1HTg007Ej23Tg01Q1j44Tg03H5j1ETg005Fj6ATg03Chj3DTg03ICj2GTg00SjR0f1R1f0R230p=5f3f2R3;01/12p=21112,13p=<g00OkR4g00<Y#6#6#6#6#6#6#J#FR51C55R6#IR7%=1R8%83R9=079R:%=3R;9072P7%>3R<%;3R=/@='9P<P5%:3R>P>P5P=P=%?3R?/5?AB31=#7%73R3'5'1C2C2R@C23<X07P7%H6R6A07;;P719<2P<P@C25<:X07%81R:=07:R@A0788RA%>1RB=07BRC%:1RD=05DRE%;1RF=05FRG%?1RH/5HRIAB12FRJ#7%71RK'5RL'1RM'1RN'1RO'1RP'1137:PAPP1378PCPO137BPEPN135DPGPM135FPIPL130H130KC4C4C4C4C4C4P719B6PBPOC29<@Ae1@FF%EFEAAD12F1G12EAPJP4P7%82P9P7%=2P;P7%>2P<P5%:2P>P5%;2P=%?2/5?%72/53'1C2C2C2C2C2b2eW3W1o"). Qed.

(* [comment removed for export] *)
(* LPS 08b1429: a brk grow records the PAGE range [page_round_up old, page_round_up r)
   (Mmap.brk_grants / brk_page_range), so the old statement (entry (vm_brk h, req - b)) is
   false for an unaligned break.  Restated with the alignment its callers already have
   (the same premises as brk_grow_ok_facts). *)
Lemma brk_model_next_grown : forall h req,
  let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  let h' := brk_model_next h (MmNodes.wz req) (MmNodes.wz req) in
  vm_reserved h' = vm_reserved h
  /\ vm_maps h' = (vm_brk h, MmNodes.wz (req - b)) :: vm_maps h
  /\ vm_noaccess h' = vm_noaccess h
  /\ vm_start_brk h' = vm_start_brk h /\ vm_brk h' = MmNodes.wz req /\ vm_limit h' = vm_limit h
  /\ alloc_top h' = alloc_top h.
Proof.
  intros h req b Hb Hreq Hba Hra h'. subst h'.
  assert (Pb : page_round_up_Z b = b).
  { unfold page_round_up_Z. rewrite page_size_eq. clear - Hb Hba. Z.div_mod_to_equations. nia. }
  assert (Pr : page_round_up_Z req = req).
  { unfold page_round_up_Z. rewrite page_size_eq. clear - Hb Hreq Hra. Z.div_mod_to_equations. nia. }
  assert (Eb : Z_to_bv 64 b = vm_brk h) by apply Z_to_bv_bv_unsigned.
  cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit].
  unfold brk_maps_next, brk_grants, brk_is_grow, brk_unmaps, brk_page_range, MmNodes.wz.
  rewrite !unsigned_wz by lia. rewrite w_is0_wz by lia. fold b.
  rewrite Pb, Pr.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? b) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb andb app]. rewrite Eb.
  repeat split; reflexivity.
Qed.

Lemma region_free_shrink : ltac2:(zQ "a0!htf!ig4!ina!io2!hi5!ioa!iia!ila!ij9!s4>4maps@1$7@2$8@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2n'@1$1@1$0#k0>0@3$4$2@3$5^4^3^2$3>0@2$9@2$6@1$0#k0^2@2$6@1$0#k0^3@3$4$2@3$5^6^5^3$3").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["HC"] "h04__x1h14__x2h24__x3h34__x4h44__x5h51Hh62H0h73Hinh83Hleh97__arithh:4__ffh;8__varmaph<5__with=1ah>1eh?4mapsh@1nhA2n'hB2szp;1p;2p;3p;4p;7p;8g007_j12Tg00HFj1ZTg018^j1JTg01?Rj2FTg00Clj1BTg01HNj3VTg00K9j3?Tg01:aj21Tg00@hj20Tg01:Aj4GTg01A8j3ETg01LLj7DTg00XZj24Tg01D^j2;Tg00]ej1:Tg00^Dj28Tg00jUj3ATg00agj2UTg00CLj1TTg00c?j3MTg00DLj2<Tg00c_j1LTg00d=j49Tg00Djj1ITg00EHj1HTg00FVj23Tg008bj1>Tg00fEj37Tg00Gdj1KTg00Ikj2NTg007Ej2OTg00JMj2PTg00KSj3QTg00L2j4CTg03QXj4RTg00G9j4STg00Ldj7YTg01EZj7XTg00IGj8WTg00SjR0f1R1g00U4f0R2CSp=5P1g00MlR3g00NKR4P4g00NkR5P2g00OKFYp=6f2R6P3P4P4P5P1P2FXp==f3R7P3P4P4P5P6P1P2GWp=@g00<YR3#2R8#2R9#2#2#2#2#ZR:#JR;/F;R<#Bg00VBR=AV761g00VbR>3?11:1R?11:6R@'0f5RAf4RBP6P;P;P1P2CGf7RC5E<f8R<PCf6RDP6P1PBP2FD11:CRC11:D'4/0@14@?/0C';g00THR@g00l]#:R?#:RD#:,80180D180?5A05A0g00m<'U%T@3M%B@P0P01<0BP6%L0R@C9P1P01<0AP7P@C9C9%I0%H0R@1303R?%>8,30RD570%>3,30R3'5,6@13099703/5?,6@R95=@%K4R4P@1308R8/5D,6@P4A70?8/53,6@==@9C@C@1N@5P2P61O=>1P26=?=>dg00S0=Q01CCb:b;b<X00X10X20X30X40142B/061467R>/02';106A10>B14BA/06';[[^00^10^20^30^40P211:<11:711:BPCf9,1:P1PAO7b9b6W7XB;X>;CRW8W5XA;X@;X=;W?o"). Qed.

(* [comment removed for export] *)
Lemma brk_grow_ok_facts : ltac2:(zQ "ha0!htf!hi5!hk3!m5!ina!io2!re!nr0!ho4!nr6!ig4!ip8!ij9!kl4!s9!pe!klc!ioa!lg9!lhd!lj5!ns1!s4!ma!jjc!iia>1m$d>3req$2=1h$e@1$h0^2=1b$2@2$h9@1$0#k0@1$h2^1>0@2$3Z^1>0@2$6@2$3^2^4@2$3^4@2$h7+2+k0>0@3$1$2@2$8^3+hgg0Z>0@3$1$2@2$8^6+hgg0Z>0@3$1$4@3$h5^8@1$7^7@1$7^7$5@2$6@2$h6^8@1$f^7@3$1$4@3$h1@3$b@2$c@1$a@1$0#k0@1$a@1$0#k0@1$h4^7@1$h3^7@2$9@1$0#k0^6@2$9@1$0#k0@2$h8^8^6$5").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "#$8\h02H0h11Hh24__x1h32H1h42H7h54__x2h62H8h73H11h82H6h93H10h:2H3h;2H4h<2H5h=2H9h>7__arithh?4__x3h@4__x4hA4__x5hB5heq_bhC4__ffhD6__sat1hE8__varmaphF5__withG2H2hH!sG%0hI!s/%3hJ2zhhK4__p1hL!s;%4hM!s/%5hN4__x6hO1zhP3H12hQ!s@%2hR1mhS4__x7hT1bhU1nhV!sB%6hW1ahX3H13hY3H14hZ3H16h[2Hah\7!tp%6h]!s0%21h^1qh_2q0h`2q1ha1rhb2r0hc2r1hd3H15he3H17hf3H18hg3H19hh2Hbhi3Hbahj3Hrahk4Hreqhl1Rhm2_Hhn!t7&5ho!t7&0hp1hhq2q2hr2r2hs3reqp%0p%1p&0p;1p;2p;3p;6p;4p;7p;8g02C2k10gTg007_j1DTg00HFk10PTg008Dj1jTg009Gk20Z!s0$dj2:Tg00Z1j20Tg03JTk10DTg03Rhk30BTg01=Nj21Tg01:aj2rTg01JNj22Tg01KNj2KTg00iWj1UTg018^k10YTg01?Rk20WTg03Shj2STg00A_k20ITg00BGk30G!tI$Qj2BTg00[2k10E!s0$Kj2@Tg00\2j2!s8$\Yj2ATg00]?j2FTg03TYj2R!sp$kk20>!uj$Ej2wTg00`?k10^!s0$]k20]!s_$ej1XTg00^Dk20=Tg00agj2vTg00bSj2fTg00CLk10\Tg00c?j3u!s9$lk10[!s9$_k10!si$Djk10VTg00EHk10UTg00F3j2iTg00d[k60TTg00Gdk10!un$8bj1{!sL$Vk20;!w^$dk30OTg00Ikk20NTg00JMk20MTg00KSk30LTg00L2k40!w%$YTj29!s/$7j27Tg017Rk20JTg01AOk60:Tg01\7k20HTg00@0j1[Tg02G9j1sTg03Udj2JTg00XZj28Tg00W_j2<!v4$mk20CTg00_Vk30FTg00fhk301Tg005Fj6oTg01IHk305!x9$DS00j2b!t8$hj2?Tg03Vfj2pTg03WCk20A!s0$ck10QTg01`lk20<Tg03X`k60@Tg01Q1k40RTg02W<k10?!ur$9j3_Tg02M=j1|Tg01FZk304Tg01HNk303!x'$>k30!w{$jUk302!w^$Lk20e!wK$=k40d!wK$9k400!vh$dj7}Tg00ebk30c!uX$Ek30a!wK$Gj8~Tg00MHk70`Tg012gk40_Tg014jk60bTf1R0f0R1$0?'rp=Qg00S0R2/:1p=`f2R3/:0/b1p=tg00SjR4?_12p=Zg00VBR5g00VbR67_1p=3g00keS01,81p=h1<01,13p==f6R7f5R8#['pf4R9f3R:#|%s3404@0301'Kp=I1J01,K3p=n1w41p=dA_401p=51?21p=61730,9:/819_49p=O1?231:01'bp=41:301?12'bp=G1701=_42p=L1:01,b3p=l20=41p=WB0f!s~$aB02401:0243p=M!s4%p=q20e41p=eP4P3P0P1H0dp=CP3g00MlR;g00NKR<P<g00NkR=P4P0g00k>P1H00g00OKR>F}p=H20;41p=^B0c!t$$]B0a!s/$YP:P;P<P<P=!t1%G~p=VP3!s;+!sy%U[!sy$P!st$T!sE-0P1K0`p=c!sO'4!sO$p=gP0!sK+1!s^%kP7!s9+8P9!tH5G~p=>18019_43p=PP5P0P6P1H0_p=zA_561p=yP5P:!sX$6P1Eop=x!t8/J0bp>09%|0>0431p>081130>03:1p>071p30/K1p>061830/<1p=;1K01=_56p=N%[1,p0p=m%|8%s96047!yS&803:p=\g02mN&0g!v}$kg00<YR>#DS02#DR?#DS03#D#D#DR@$0PRA/Q1P4%`1S04Q02#jRB%j@RC+0ZRD,::9t0:%D@!sY%S05!s/$jR@,03#Z108@#Zf7RE&0D7RF<0BF#3P411AERF,rAP5P51QAERG,2212G1'KP5P5%UGRG%U1RH'2PHPE&0YARI00WIRIPEPE11AG%hH==AGFIP6n010!s#$20000f9RGf8RH,1A3n!sC3#3XO4P1PE1QA7RJ#d158JRKePK1S7@%67RK%6@RL10H@#6[[20IBCRM%`BRN%6C%`D[RO[RP%6BR!~>$NRRB0GBC0UW[RC%6DRS\R^[QRTf;RU/S@S06%6Uf=RV/0@RW#6\L[S07f<RX/B@%Z@RY$0ERZPVP@!s&$WDO[1@V@%`@RWf>R[/0@R\?4\@[1E[@1:@2R\f?R]/0@R^=G@^[1A]@f@R_/L@\Y1F_@fAR`/0@Ra/5`\Yg01F>Rb1R`@RcePc1B_@S08P`P@!s&$aDO\ZS091@`@S0:fBRc/0@Rd?4d@\WS0;1Ec@S0<fCRd/0@Re=G@e\\S0=1Ad@S0>fDRf!tJ$S0?1Ff@S0@fERg/0@Rh/5g\YS0APb1Rg@RieS0BPiP9g00:@Rj20>2@'wPWeS0CO1S0DfFRk/0@Rl#6S0E?ll@S0FPUQ!sE%GfIRl/0@Rm?4m@S0HP3PRP`P1P0O2XWQS0IPS^WQS0JPc20>2B,wjPNeS0KO1S0LPOg00THRN&0^>-0]4Rjg00l]RS#XRn#XRo#XRp#XRq#XRr#XRs#XRt#WS0M'aRu%WsRs%WrS0N%WqS0O,ajS0P%WpRp3M3M1ajsS0Q%WnRn5Mu%XtS0R#X#WS0S?Msp%WoS0T20=4SS0U,qnS0V'qg00m<S0W'v'f'f'f&0\NRS3u&0[NRo%e9S0X%e8S0Y7C3&0X4Rt%e7S0Z7C:7C0&0V4Ru&0U4RqPqPq!#3T&1i4@R;1i42Rr5HqJ0TS0[&0S<R<Q02#^Rv%{>Rw#{#^,];S0\%^wS0]'Y5HqCVP<PqPqQ0[P<20;4>Rx%Dw#^S0^,];%^?S0_!sP-Q0_=HqrS0`!s4%]!s4%aP<PqATqvxS0b1i4B>0O4AS0c9TqxRB5cq!sG&rvS0dP<1grx,kq=cqBF>F>F>20Nq=R=P1P31w5620M13#3dB0L420H0KRBbCbEbFX24X54X?4X@4XA4XN4g00mh\YR?19@7Rw=P3:[AP3w8\?%Z8S0eQ0e1:9D9t89%`7AlK7D[!s#$^24^54^?4^@4^A4^N4P1fLRK/7@S0ffNRw/7@10w@Ry10K@S0gPKPwPUP`fHRzPlfJR{fKR|O<b>bQbDbJb3b4%6zS0h?lzDeb7b9b=b6b4b8b<b;b:bGb3b0bHbDbQbIbB-0JEJ0:P5P5122J12JE!#5q&JRJ%UER}'2P}P7PIP7P711AJ%h}==AJ!#5g4?nHF!#5^41227RFQ001201#31:30RJ[1:011230#3[R~12:3#3\J20H01P1n20!sj'1!sk$000XR4XU4S0iP~^R4^U4S0jP1P2PE1QAHR~#d15E~R~eP~1SH@%6HS0kf:R~/0@#6\L[Q06Q07PMPPPCPT1B[@P]P!s&%^DO\Z1@]@10_@RJ?4J@\W1E_@AG@aa\\1A`@1Lc@\Y1Fc@15ed\YPb1Rd@RaePa1Bc@PdP!s&%e!sr%d@10f@Ra?4a!sr$f@AG@hh\\1Ag@1Lk!sr$k@fGRa/0@S07/5a!s{%a@RJePJQ0D10z@S06Q06;4@S0lQ0G10|@S0mQ0m;4@P3PRP_!#4?,nQ0JP`Q!#4/$oPOPSPo%e0Pu!{_%xRQP<PQCVP=P!{3,Q04%`0[^24P1PwfMRQO2b>bDbH!yd&`z!y]FO3b0'z%yF122E!yc%H~R2,K1!yb%HRF%U~RJ'2PJPGPIPGPG11AF%hJ==AF!yb511A~7nU!ye5XT5P0P1Cx!t4%EG,K6!#=a&F,2}PFPHPIPHPH11A}%hF==A}!t-8G7n~!t-5Q0iQ!yq$GPU1QA~R}#d15G}R}eP}1S~@%6~10X!yk%1SV@%6V%6^\L[!yr'Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BPi1Bf@PgP!s&%h!yI%g@Q0F\W1Ek@Q07Q075G@\\1Aa@17z@S0F#Z\Y1Fz@15ml!yB%l@RhePh!yB${@S0BQ0B;4@!y?$Q@Rh?4h@S0AP3PRQ!y4$Q0oPOp-0Rh!y2%3?C0tS0@!y9&xvRi209q9!#6,$i!yA2X54WKS0?At1031:03!#4o&KhS0>P1fRRi/:DPifPR^PwO4!y^/1:{K!y_J,z2%y212GU!xR$K6!y[&XR2,2J%[US0=%sU:08IUS0<PAPJ%h2==AJH076062!x[6XS0;,JVR2'K!yjCK6!yg&URJ,2FPJP~PIP~P~!zoCU7nX!t'5P4Q0!u7%j>R>9;U1/71/91RFA;V1>!s3&!|$%XPIPXPX11AF18J1!t8<V,J['N!#E8$@g00n!#7j&A;~@>/7@/9@RFA;X@>RJ/7@R}/9@S01'2Q01!zO$<PAPFQ01/8@==AFH07406!t80100/N2A;U@>S0=/B@19@}10J@5PJ\Z1@J@A;V!t-$0@R}?4}@\W1EJ@A;[@>S0</0@RJ=G@J\\Q0</A@A;]@>S0:/7@S09#Z\YQ0:/F@18_@S08/<!sr%S04/5J\Y17J@S0pP4A;`@>S0q!sB$rP418f@S0s/<>S0t/B@A;g@>R}P@P}P@10}@S0u!|a%}@18k@S0v/<>R}/0@R2?42!tv$}@A;a@!s<'=G@2\\1A}@18z@S0w!sW%!#Fd$}@18l@S0x!sl'/5}\Y17}@P4A;{@>/0@P41B|@S0yQ0f,9@Q0g5PK\ZS0f1@K@S0zQ0A\WS0A1EQ@S0{AG@yy\\S0|1Aw@S0}fORy!#FX%~1Fy@S1010^@/5^\YS1117^@S12P4fQ!tQ$S13P41B^!uj$P}P@Q13!uj+0i!u_-i@fSS14/0@Ri=G@i\\Q14/A@fTRi!uW&i@fUR2!uO$2\Y172@P4fVRF!t6$5P4P8!#G:$16A411@S17PV!s8&8Q0k?lH@S0kPg!s:&9A4__@S1:PQ!s8$Q0h?lz@f\S0h,QAS0C#df[S1;Q0C'5S0CeQ0C!#6;&P0!#:^%KPOQ0N,aj1ajnQ0U3MQ0N1ajpQ0T'q5MsQ0VQ!#FH&Q0NQ0V'q20C4@Q0U60F4S0UQ0QQ0OQ0T,aj7Mp3M!sW&=uNS5uNS0QPo%e:S0OQ0Y?C9t7C3?C0tPu!#Eh'Q02#{S02#D#^,];Q0_'Y9Hqx!#Ec&^,gr,kqQ0^=Tq;5cqS0T!#FO,1Yx;S0V1i4>60141];vQ0^!#FM%S0^!sk%`P<1]v;9HqxS0NF>F>!#6v2!#EF'19@8=P0:\?A499@A;:@>19@9;P7\?Q0e198@,59!#E45S0eP1P~PwPGPyf`P]P8Pif]S0CO9b>b]bob]bBb3b8b7bZbrbqbgbfbebZbdbcb`bYbXbPb7b9bbb_!#7l,ab^!#7p+Q0=!#4,$,5U!#5P'Q09/9@R~,21P~P[PIP[P[11A118~@==A1!#5;110011A]S09,J_!#5>$0PXP1Eo!st%<!t1%S0<,2XQ0<PVPIPVPV!#<_$!#5%$X!sz8[S0<,J]'NQ0:/B@Q0p!}d$4!#5&'Q0rQ0r;4@\WQ0q/E@18c@S0q!#4L&RX=G@X\\1AJ@18d@RJ/<>R>!|X&>@Q0t/0@Q0t'5\YQ0t/7@P4Q0uP41Bk@PaP!s&$Q07!}d%a@Q0l\W1Ez@AG@mm\\1Al@1L{!su${@Q0m/5|\Y17|@RmP4Q0gP4Q0yQ0fQ0zQ0AQ0{Q0|Q0}Q0~Q10Q11Q12P4Q13P4Q16Q17Q!}[$Q19Q1:1QAFR>#d152>R>eP>!#@B+!|~$QPoQ0X9Ct3!|F$Y7C87C0!{u0\!#O8$>!{m1T!{t&P<PqAHq>rP<Q!{0BQ!zN$_PkP]PaQ0hPgP8PKPF!zL$\bnb\!zL+!z<L15]~P4Q0p/9@!#DN$]1!t3$IP_P_Q09181@R~==A]!#<F7`!z1$c!z1'_!z1'12[_P_P]PIP]P]Q0<Q08==A[!sk8_R[,J`'N12]`R]!#D~'_Pc1QA`RX#d15_XRXePX1S`@%6`%6e\L[1Sf@%6fQ0E!#D{,1Ba@Q0F!zd$65Pz\Z1@z@Q0H\W1El@Q0BQ0B!#DX%{@%Zm\Y1F|@Q0g/5K!#DT$K@RmePm!yLAPb1R^!sO'DQ13#6RmQ13;l!#D}$i@Re?4e@!#Dz1Q0?Q0>P1fYRe/:DPefWRXP2!#D%0Q14,:}!#JdM]12_cP5P5P1PdPcPIPcPcQ09A=AJ`FIRJ!w<6dR6,JfR]'N!#CT+cP`PIP`P`P[Q0q==A_FI11AcR_,Jd'NB05J]1%3J%3]'bQ001mfdPIPdPdP_PAQ0sPcF\'N11AfRc,Jg#3%[f,?gPIPfPfP6PAPgPdF\#3'bP11mkgPIPgPgPcPAQ0vPf!sd&aRf,Jz#31mzaRcPIPaPa11AkPAQ0wPkF\Rk<050%3c%3k!tX&lz#3PIPzPzPfPAQ0xPaF\#3%[l,?{PIPlPl11AzPAP{Pz!tQ,|{!s]$|P|11A{PA18K@P{F\#3Q001p01#31?30[R{1?011p30#3RK[1?:3\K20A01P0!#T-<P{!#T'$P1Pw%[QR{P3O31?w{%[wR{,?yPIPwPw11AQPAPyPQF\#3P1&0Qwg03Z1,8{g03Zn':%sy:08Iy11AwA;^@wRI,1AR{1<^wR^,1AS00P:P4P^18}@==Ay,rA,?1XO4P4PI1<}y/!s4$1QAy!#Nb$w}R}eS0xP}1Sy@S0w%6yPm\L[S0v!|]+Si@S0s%6iQ15!#dQ%q1B2@S09PFP@PFP@Q15DO\ZS151@F@S1410X@RF?4F@\WRF1EX@RXfXR2/0@RL=G@L\\RL1A2@R21Le@\YRi1Fe@RmfZRy/0@Rw/5y\YRQPb1Ry@RKeR|PK1Be@RePyP@!s&$wDO\ZRZ1@y@RyQ1;!s^$?4w@\WRWQ1;/E@RwQ0h/0@Rl=G@l\\R\Q0h/A@RlQ0C/L@\YRfQ0C/F@Rkf^Rc/0@/5c\YR!~e$c@RceRbPcQ0Df_!#dc$d?4d@RdQ0GfbS0C/0@R6?46@R6!~F%I!~F$L!#VI$Q0@PuB014xvR_Q0V>014vR]'g,kq!#8421<101<~0'?!#?l$P1feR~fgRJO2b>bMbLbJb0b6faR[/<gR5A;[@gRg'?e!#84%!#3/00b1bIbLbMbVbB1rA{Q0xP}Q0wQ!xJ,Q0sQ0qQ09Q15Q14PFPXPLP2PiPmPQP|PKPePZPyPWPwP\PlPfPkPYP!v/%PdQ0GP!ul3Q0R#W?MpnQ0UQ0S,ajQ0MQ0P/qn7Ms!#D}/RSPo%eE?C9t?C3tQ0YQ!#dd&R!#D~03!#Dw%]'Y9HqvCVRv!#D_,Q0\!#E:,R;!#<F$3#jR9,i4Q05#jRN,i4Rs']/]s,Y>Q0c5TqRsP<Pq1gx>,kqR>!#E-'PqQ!#dJ$Q0b209qG5cqRx!s7%!#d5$],kqQ0c9Tq]5cq!#d;$!#=M=XN4XS4XKh19@ER]=P3:\?RnAP3]8\?R?199N/9N,87/:DRN1?:ER:%ZER9AtE7VRV%`HREA;H@GR7?47D[[\9!#d<9^S4^KhP11:JD17~@17J@ff#[10J@10~@P~PJPUP`PaPzP[Q0CfcfdO@R[!yy/A4ggD!ylF-0<IEoQ00,rA!yt~!|b1P!y2%!xp%!x[$P!x7$P!x06P!w}0_!w}+_!w}Q<HGRH?4HD\E\V\9\9\:\N\?\n!wF<!vm255!vmJ^EoJ0@blH0Rb3b1WGW3P0P1O2!#9W/!s/&b1WmW1!sF?b1!t0$!s&'!s0+W1WjWiWkWhbTbpXs4WRo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post : ltac2:(zQ "50!hk3!mk5!kl4!jk2!mod>1L$3>1e$4>1G>0$1>0$2P>2s0$1>2cb$0>2ck$0>0$0>0$1>0$2P") := ltac2:(zQ "h80!re!hk3!hi5!mk5!kl4!nt0!mkf!nte!ml8!jjc!ina!ij9!io2!mm1!nu6!jk2!njd!kq7!nv3!nvf!ogb!mod!oh7!ohf\1L$f\1e$h5\1G>0$3>0$4P\2s0$3\2cb$1\2ck$1\1z$1\1s$3\2mo$4@2$0@3$2$a@3$e^9^8^3$c@2$0@2$h2^8^3@2$0@3$h1@3$5^9^8^3@1$h7^2^1@2$0@2^7^2^1@2$0@3$2$h6@1$7^2@1$7^6@2$0@3$2@2$b$1$1@1$6^2@1$6^6@2$0@3$2$d@1$8^2@1$8^6@4$h0@3$5^9^8^3^1@2$9^5@1$h3^8@2$9^4@1$h4^8").

Lemma KLB_rephase : ltac2:(zQ "a0!hk3!oi9!hi5!kq7!jue!khd!kl4!jm1!jk2!oj6>1L$8>2ph$7>4pbrk$0>5pbrk'$0>2mo$6>0@3$3^5^3^1>0@4$9^5^6^3^2>0@3$2$0@1$4@2$1^6^7@1$4^7>0@3$2$0@1$5@2$1^7^8@1$5^8@3$3@2$1^8^9^6^5").
(* Replay replaced by explicit text (rule 11); the zQ STATEMENT above is
   untouched, so no caller changes.  Proof from
   a donor tree
   projects/boost-beast/http_request/proofs/lib/Spec/KLink.v, its KLB_rephase,
   verbatim.  Binder check against this tree's own zQ rather than assumed:
   five binders (L ph pbrk pbrk' mo) and four hypotheses (KLB, phase_inv, the
   lbrk_bytes equation, the lbrk_cnt equation), which is what the donor's
   intro pattern consumes. *)
Proof.
  intros L ph pbrk pbrk' mo K Hph Hb Hc. kb_open K; constructor;
    try exact Kresv; try exact Krtop; try exact Kvdi; try exact Kvdd; try exact Krdr; cbn; auto.
  - unfold ltotal in *. cbn. rewrite Hb. exact Klive.
  - unfold lcount in *. cbn. rewrite Hc. exact Kcnt.
Qed.

Lemma lbrk_dead : ltac2:(zQ "e0!hk3!hi5!ok3!oi9!jue!khd!re!it4!im2!okd!jm1!ola!jme!jk2>1L$d>0@2$8@1$b^1@2$7$0\1c$0@3$1$a@1$c^2@1$9^1@2$6@3$1$0@1$4@2$3$2^2@1$4^2@3$1$0@1$5@2$3$2^2@1$5^2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##<Lp'0h01ch11Hh23curi003curh31Eh41Lh51bi011bh61ei021li031pi041xi051zp;1p;2p;3p;4p;6g03`Fj1HTg02c1j1?Tg03aMj1;Tg01D^R0j24Tg01?RR1j2FTg02`Aj11Tg007_j1BTg008Dj19Tg00YTj2A!s/$7j2@Tg00W_j2GTg00ADj26Tg00K9j37!se$Ej28Tg01Q1j4=Tg03bVj15Tg01AOj6E!s/$kj2DTg03\oj2>Tg03^6j1:Tg03_?j1<Tg01WUR2j2CTg030JR3f1R4f0R537p=3g00SjR6/C5p=2A7645p=0g02lJ%H5%?4R7%;5R8'3X06#2'4P7P3P3P3p-0R9P5g00SNR:g00mhR;P;P:P:n01104000500101!s'&00001348!sn&g02AYR<1F66R=P6f4R>#1R?P1P6!s$$5P5n2001103000120105102R@g00S0RAn1!t4'210!sK$RBP3P6P4PBP<P=P6f5#1RCP@P!sR7Dg00<YRE#B#9g00oPRF'ARGPBPB!u5='0!t$%P!tu-1@5F%9ERE'G!t~8F!tM81!ty&1!sw&CP!sN9CPEP1P1!ta?'6]1P5g03c_=73!v}%,4:!uz&3R1!vu$!u|9B/0B!uI+!tP9?/0?186B186?C=R?W1%;4RB/!t8+;10DD10CC186D186CC=W1X26P5O1%54!sO-P0P;f2R0#5!s;'!ts&6RC#1RD!ts9/0G!tq&D!tq9/0E'6P5P;!st&8!srcRDP5n!w#'0X1;!uA%1!u++2P6%5>!s5%PDP5%5C/38P3f7#5P3P9!t[$;P:P;P;!x%$1!x%7X63g01F>PBP5EE!u5+<#1R;!u5C;!u5>/D5b1W3X06P4P5O2!zU$!}6&20!sW%W1P5O1!s@-2!s-$!s'$!x++g03dh!yj0?W1g03f1R;!s=3!u]51!t$&b5P5O!{V$1>;4R5#?R?!u<%%15R:!zX:8!sI%1>;0!v-=PGP8P8!|'=!|s$7!t;'4R8!{m;!sI'0R0!t8<!~xC3!|S$!we%:!|[::!x,APE!#6=@!uF/P8!t2:!vX&P0!t2<!vR@'0'6e%:5%:4'0%<5%<4!s9$W1W4o"). Qed.

Lemma mspec_get_bind_eq {A} (s0 : PState) (P : assn PState) (f : PState -> MP A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##1th01ph11sh21xh32moh43mo'h51Ah62H0h71Ph81Qh91fh:2s0h;1Hh<2HPp;1p;2p;3p;6p;5p;4p1003<p4p70R0g03g:R1p4p7210R2p8P0g03h>R0p4p710R3p8p1006A!sX%4P2p8P4P3p8p200R3g015NR4!sh&p8P3g016NR5p4p731!s9%!s[$3g03iBR2!s?/g005dR6!t:%p8P0j1DTP4j2CTg00K9j30Tg00ADR4j26TP2j67Tg01?Rj23Tg03jGj1:TP6j32Tg01>4j31TP1j54Tg007Ej28Tg01Q1j49Tg03kJj1BTg01:Aj4ATg03lQj2<Tg03mXj3;Tg03n]j5=Tg005Fj6>TP5j5?j6@Tg03o`R5P5f3R1f2R6f1R2f0R0E@p=5%D5R71C51\5R8P7\1R9g040fR:P5f4R;g02mNR<f5R=9052P;P2P0O2'6W3X15P2P1O1P0E7f6R>!sG$=!sG'R?P4f7R49056P>P6P2O2P:f9R@/35RAP@%:5RBP4P0O1X25P1C5P6P4f;RC?252A1C52P0O3X4<X0AD4P0A05;@P5f:RAPAP0P=!sw$=RD/35REPDPBPC!st'2C5P>PCf?R>!st%>!st-ED4[X15P@PAP;O2P4PCP=A05CCPAPCP=O2185CP0C9O3P:f<R4/35R@g041mRE1355R>P@%B>P5P5PCPCCA,<>5;EPAA2550A1550O2X0>D=P=PAf>!tT7@R>D4eP:P@P4PBPA!u1'CC5P=P>D4eW<P=P0E>W6!vs%n20010!s#$12!s-%0W6X3<X15P:P5P=P?!s4&5!s4$BP1!s|&D?P2E7eW;X89X98X77X:5X53P;P1P!t,%5W8W9W!s>&o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk0_ok : ltac2:(zQ "h90!mk5!hk3!re!mm1!hi5!kl4!oq4!oqd!ov4!ovc!jm1!jme!jk2!njd!kq7!pg9!ph9!pm3!pmc!pn2!pnc!po4!poc!ohf!pp4>1L$c>1G>0$0>0$5P>2s0$0>2cb$1>2ck$1>0@1$h0^4>0@3$4$a@1$b^6$9@6$h1$h3$0$1\1s$0\2mo$5@2$2@3$4$0^2^7@2$2@3$e^9@1$h7^2^1@2$2@2^8^2^1@4$d^9^1^6^5@5$6$0$1$1@4$h5$0$1@1$8Z$7\1r$1@5$6$0$3$1@2$h6$0@1$h8^1\0$3@3$h4$0$1^2@6$f^7@1$h2Z^6^5^4^3").
Proof.
  intros L G s0 cb ck HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KLB (set_brkph (BPQueried r) L) r mo /\ BUD L mo cb ck)).
    intros s mo (-> & HK & HGs & HB). split; [cbn; lia|].
    intros rsp mo' evs Hst.
    apply (fun X0__ Q1__ => proj1 (nstep_brk_iff mo _ _ _ _ Q1__) X0__) in Hst; [| lia]. destruct Hst as (-> & -> & ->). rewrite !brk_result_query.
    pose proof (kb_minv _ _ _ HK) as MI. rewrite (with_brk_next_eq mo) by exact MI.
    pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz 0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    set (h' := brk_model_next (m_vmmaps mo) (MmNodes.wz 0) (vm_brk (m_vmmaps mo))) in *.
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split.
    { unfold dec_brk0. cbn. unfold brk_zeros, brk_is_grow. change (w_is0 (MmNodes.wz 0)) with true. cbn. rewrite brk_unmaps_noop. reflexivity. }
    assert (HK' : KLB L (ps_brk s0) (with_vmmaps h' mo)).
    { eapply KLB_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)| ..];
        cbn [m_vmmaps with_vmmaps]; unfold m_vmmaps, with_vmmaps; cbn;
        first [assumption | reflexivity]. }
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Evm : m_vmmaps (with_vmmaps h' mo) = h') by reflexivity.
    pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as R. unfold bv_modulus in R.
    splits.
    - reflexivity.
    - eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
    - unfold brk0_answer_ok. rewrite Ebrk.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KLB_rephase; [exact HK'| | unfold lbrk_bytes; cbn; rewrite Hph; reflexivity| unfold lbrk_cnt; cbn; rewrite Hph; reflexivity].
      cbn [phase_inv]. rewrite Evm, E5, E4, Ebrk. splits; auto.
    - destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD. rewrite Evm, E6. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. intros s mo (s1 & -> & -> & HGs & Hans & HK & HB). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb ans_cont ev_costb ev_costk].
  rewrite Z.sub_0_r, Z.sub_0_r.
  splits; auto. { eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs]. }
  destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount in *. cbn. unfold lbrk_bytes, lbrk_cnt in *. cbn. rewrite Hph in B2, B4. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_dec_brk' : ltac2:(zQ "i21!hi5!htf!lg9!iia!re!nr0!kl4!pq2!pqc!m5!ll2!ila!jka!lvb!npe!pr4!ina!no9!io2!im2!hk3!s9!klc!lk3!ns1!pre!ps9!qgf!ov4!qh7!ql7!lg0!s4!ma&@3$f@2$3@1$1#k0@1$2^6^b^9>3req$h4>2mo$6>3rsp$hb>3mo'$6>3evs@1$b$8=1h$h5@1$h6^4>0@1$hf^5>0@2$9Z@2$3@1$1#k0@1$2^2>0@2$i0@2$3@1$1#k0@1$h7^3@2$3@1$1#k0@1$2^3>0@2$4@2$9@2$3@1$1#k0@1$2^4^9@2$9^9@2$i1+2+k0>0@6$hd$he@1$hc^a^9^8^7^6@2$4@3$0@1$b$8^7@1$h1$8@2$h3@2$4@3$0@1$c$7~0@2$a$7$ha@3$0$6^8@2$d@3$e^6@1$5^b@1$2^6^a@2$4@3$0@1$c$7~0@2$a$7$h9@2$4@3$0$6^8@2$d@3$e^6@1$5^b@1$5^b^a@3$0$h0@3$h8^a@1$5^b@1$5^b$h2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "#$&2p'0h06__sat1h11Hh24__x1h31bi001bh47__arithh5!sM%0h64__x2h74__p1h84__ffh98__varmaph:5__with;1rh<3Hgoh=3evsh>3mo'h?1xh@1yhA1zhB1mhC3reqhD2HahE4__p2hF3effhG1li011lhH1ni021nhI3rsphJ2H0hK2HbhL4HreqhM3HsbhN2MIhO1RhP1hhQ2moi032l2i042loi051pi062p0i072zsp%0p&0p;1p;2p;6p;3p;4p;8p;7g00ClS00j1iTg02C2j1KTg02@Sk10GTg007_j1UTg00HFk107Tg02ROj1nTg01:aj23Tg00@hj2_Tg009dj21Tg008Dj1w!s8$Gk20;Tg00ADR0j24Tg0448j1uTg04jWj6s!sC$_k20QTg00BGk30P!s0$kk20I!tS$Ej2DTg00]ej1qTg00^Dj2eTg00jUj3oTg00agk200Tg00CLj1WTg00c?j3!sp$DLj2}!s8$_k10!sp$d=k40C!sC$jk10ATg00EHk10?Tg00FVj2x!s/$3k204!uv$dk30<Tg00Gdj1v!s/$9j4^Tg00Ikk20YTg00JMk20XTg00KSk30!tU$L2k40VTg02W<j19Tg03JTj1:Tg04<`j2BTg018^k105Tg01?RS01j2hTg04=kj35Tg03Djj2=Tg04A>j3J!t-$9j30Tg04>ik80HTg02AYS02k103Tg052kj3\Tg02aHj2rTg03Rhj3XTg01=Nj28Tg01JNj26Tg00iWj17Tg00W_j2a!xJ$Aj4VTg03KWk20FTg03LXk30ETg04CRj6CTg02;dj2<Tg01KNj22Tg0541j2>Tg00[2j1|!s]$7k20!uZ$H0j1`Tg04DPj2NTg01\7k20@Tg012gj4jTg055:j2zTg04Wij4yTg01AOj6bTg017Rj2cTg005Fj6?Tg03AEj1mTg03POk20>Tg04XDk106Tg04ESk102Tg01Q1j4gTg01DDk30=Tg03Bdk10JTg03CDk10KTg03H5k10LTg01Cjk30MTg056Fk40!wq$Z0k40N!x?$dk70OTg00MHk709!xq$Gk80RTg03G2k30STg03<<k20!w/$D^k20TTg014jk60UTg057Vk20\Tg058bk10[!zT$[k60ZTf1R1f0R2#9'3p=Hg00S0R3/12p=Y1_32p=Rg00SjR4P1g00U[P2C^p=[!s4$MlR5g00NKR6P6g00NkR7P2g00OKK0Op=Gf2R8P5P6P6P7P1P2K09p=Zf3R9!s<+8P1P2L0Rp=Ag00VBR:g00VbR;702p=@g04l`R<f6R=f5R>f4R?P9!s[%EC30p=Fg02mNR@?012,48p=SA0981/42p=]B0S9810082p=;A0>?9A0@!sC$'4p=I!s8,'400T2p=LAJ81290@9p>01f7RAP=A5>?!tA+p=pA0@12p=fP>P!tZ-9\A=p=TA\981=0?2p=Eg01KlRB90:2p=QP1!uj+2J0Up=~P:P1PBP2Cjp=lA0:B2p=t20\12$0[p=M!sX1Zp={12;2p=OP:P;!tH+?p=dP:PB!s7+bp=kg04mbR5#iRC%K9g00Ok&0G?g00<YRD#URE#U#URF#U!s-$G$07RH/H1#Y%n8,3H1HH8'_1HH9f8RI'1%wERJ%wGRG+0;RK,1I'4g04kZRLf9RM#uPIPAP=P>Es20QJGRN%YJRO%RG%YK[RP[RQ%RJR!yb$NRSB0PJG1UWDRG%RK\S^DRRR!yi$:@20I3J'DPOeO1ROPPg00THRSg00l]RT#qRU#qS03#q,e41e4U1e4T5o4S045o4g00m<S05+00%WSRT3P%iSRUP41}48P1&0D4H0CS06&0A4RV&0?4RW1x4ERE1x4DRD'[,GWRX2044J>0<4H,[D,GWS075ZW%v6R6PW20443S08/[E!sA$9P6P4Q08g00U4RJPDC^!s>$:Q!s\$S0;CACA20YW7R7P2P81D:;S0<20X28#@dB0W431H0VRYb8b9b:X24X641112S0=112K'4%Y8S0>%R8118K'4S0?[[^24^64P2%9MRZ,3HR[f>R\P>PAO4b4b0b5b0f:R]#R11]K'4%R9119K'4R^P0PL%u?f?R_!yN%EsPCP8%W5R5f@R`%:>Ra'B&05HRbP>P2&07F$05#i,hb#WRF%:=RcfARd#K#9Re7521=2eRfg04nX#WRgg025=!sS%hFFAJdc27S?b;C][RiA0C15Rj%:?,B_PbP?P2PF%K`#9Rk95a21=2kRlPgP!sa$`a27S9b;'4PL%u>P`!}-%EsRa[PCP9P51BdcPbP=!sm$:ARAfBR=!th$c!th%c!sr'=A27S>b;C]\aPLg04oPP_!}~,L0HP1n20010!s#$12!s-%0UX=CX>@XF<XC4Pi\^^=C^>@^F<^C4P2f<R^P]PMPIP1P8O6PCPIP5f;RI%:^'BPbPIP2PFf=Ri#:RL%K^#9Ra!tj%a!tj'^L27S]b;C]P0A0CM51B^LPbP^!uM%\RL%Ki!s^6iL27SIb;PCP]P5g059iR]$03RaA\[\^R[g05;1,r]R>PIPMPLPZPiC;PaP[g05<9,r]R[!s@&LPiC;AXiLL#@EIELC]P2A0CI5PCP5%:dRI,B`RLPbP`!td%=RM?52ePf!t\'dM27S_b;Pa%9iRf,3H?\=`ReP>P_PiPMPfPd!tK$eP[!s8&MPdC;AXdMM!tC%RM,4j[X=C%:`!y7%_P2PFA5I2kP!y,,I27S\b;P0P_PL!sE$Lk1=Lk!sG%P\P`PIPLH01A0C55RL/4MP2PdfCRM#:RI,B=Rk!s]$kc1=k!y9&P<fDRk#:Rc,BMRIPFPcPI%KM#9Rl1=I!tL$GpfERl#:Rj1BkjRi5JkS0@,f=Pa%9dRe,3HRffFRZ;\1RAP>PMPd%:ZRmPePlC;RePaPAP[PMPdPmPm!s:$AAXlmmRn#@RoEIEL,4L[XI<PdPMPcPIH01P@Q0@PaPfPZ1BlmRIPF%KlRc#9Rp95mI1=Ip!tl$TRIP>P2PePaPIP[P2PAP!sz$RI,4LX>@PLPa%9`RL,3HS0APlPiPF%KkS0B#9Rq95ji1=iq!ss&rP>Q0@P`PjPLPkC;S0CPaPrP[!s<'j!s<%DAXkjjRr#@S0EEIEL1DC5P@Q0BPjPiPkC;PIXB@PbP:PbPrPjPqn!|v'!|u$S0F!uU%!x[%m2p1=2!uI'fP>PcPmP2!vL$m!uS$fP[Pm!uS'X3bPrP:1D:2A0:n2P:fGRnfHRr#:Ro;Xo=0:2Pa%9kRA,3HRmfIRf!tY$1%:fRePA!t\1RcPFA5ecA1=cA!vv-kPePcPrC;Rc!s2$APr!{5$IP[P!s8%ePrC;%@1EIEL]<P1%:nRc=XZcS0G#@Pa%9MRc,3HRIPrPoPFA5ooc1=oc!t4&5!yH$oPoPnC;RC!s2$c!s2$L'fC]A0a5[S0H1fCCS0IA0:;;S0J'4R5'4Q0HP5P4PrPaPmPf18HfR5PFP5P5PAP:1hb!#>U$s163mS0KP:Ps%72Rt%7mRu'6PbPb18Ht1aut,8HCV%W5Rv5P5Pv!v=1!s64!{~$P[DEXA4%7r%7I'6RwP01612S0L#Q1_18S0M[1_21S0N1681S0O#Q[RxQ0M1698S0P#Q[20F12P2!#7+6X@4X?4Px^@4^?4P2%7fS0QPuPNPQPGPRPOPPp-0RxPTPUQ06PVPW1[D!#==$R1~W?S0S5ZWS0TP6P4PDPJPE!#=D%UCAP7P!#<p/W71121/48S0VQ0M!#<_%^7xP2fMRJ/1KPJ1HHrR?Pk!#<a+:0EmfO3b1'l%twPa%9lRw,3HRyfJRz18HzR{PFA5{{wS0WP:Ps163yS0XP:PsP2PbPb%7zRw,8H%7y/aw!wN$=P5v!wJGEC!wJ$3:Q!xK$:!s{&!sb490svP21DsvS0YQ0Yn011!sD,b3P:PsQ0K!s_:sPvPa%9Z!uO%|fKR}18H}S0ZPFQ0ZQ0Z;5wRwP2!ta-GsP4PzP:Pa1<2|Q00P5P:PwP;PBn101107!t1%20105101S0['2P>!sW&}1M|},>wS0\'2P[%v]R]!tg1!s41=0a[XA41<zy!zD$<12#QA0481#|R~[A0412#|1<81#Q[S0]1<98#Q\~20B!z<AS0^Q0]!z@%S0]P2P}P|!z?/!z:-Q0S9ZWXS0_!z,%g00k>S0`!z3&,{W!z35X7xQ0=!z3$aA0418g00mhS0b[!z>0ORE/1KS0c1HHzRXPEPZ!zA,!z<,:Pa!w0&fL!yi$S0dQ0d%9nR~35S0e!wE<,2!wC+wwQ0e13H~R~/MwS0f'>S0e'2P[P!wJE3:!tS%e,2!sW6!sI+1<}3S0eP:PaP:Ps%`2S0g163~S0h'2Q0d,3HS0d,6~'2%7~Q0d#7'N!z[3Q0f'>#O!t6<Q0eQ!x-$P2PwP3!w}/Q03,e4Q045o4Q05+00=PS!x9/_P6PWQ!#Id$PDQ0`Q08!x5,!x7:aQ0>A0483Q0b[!x01PS0a/1K1HH}S0>Q0aPnPfO5!x21Q0e#t!v3'Q!v0$?!wB$18HJ!v1$g,6?'2%7?Q0g!v171M?J!v2@P:Q0hP;P0Q0L#@1181R0[Q0=Q0O#@[RnQ0P#@\020@!|#<B4XH4S0PPn^B4^H4S0=P2P3P?!{~31}41S0O!vo%8/[D,GWRDP6PD!v^2%Y2%Y1[^24P21HHwS08PzO2!v;/CjQ0h90:;P:P;!yN,BS0h/221HHfRDfNRn,8H,3HR0'6'2%7DRS%70!vE7DnR0!vGA4PJ!wQ,h/2;S0h16D2'21NSt!sx3/>0!ss<A4P:16?JR?P;Q0PQ!vN$DPn!#3N;TP6Q0R!y{8S0RQ0V1118!yu,S0VP2fRR8/1KP81HHJPf!~}1CjA0:;?!vZ/!uJ$2%7XR?%7ES0T!vD7XE!vB@%7nS0=,6S!#9r%a!#:s+Q0>#7S0>,8HQ0a#7Q0>'aS0a!#:}'R8!~,521h44RtPsP:&03tP2P4P4Q!|=$CV,rt%vt!sY31P4P4!tC'18H118H2!t0%!z{$106!z{%104102Pv!#5U$5000210!sD$'>!uW9P2!uI$!#4v<S011Da[Rt!tJ&?Q0T/a?!uY,?/>?Rb%@bA0s88[A0s??1>88#@[1z??1Ds?CyCdQ01Pt1>vvRt%@tRtA0svvR?[Pt\?1zvvQ0YCyCd!#=K%1020101b3!#6h$=,NSRS/>0!tu9e!{&1PS!zwNe16DnP2Ebb1Q0g!zl5!~8&:1~W95ZW!#60$S!#XV$P6Q!#XX$!{&17xXExR0%R2/41111K,49Q!#X,&7x^ExRxP2Q08fQR9'1119KP9PZPr!#6%+,cJE?Q0e!tg%1<w3P2Ckb1Q0Z#m!ts00PxP211XEQ0cPEPkPZ!sl,-0>}E?!va%\!uw=<}}RZ&06}Cd!sR%[,2B!#;p$Q0\,2Z!#;\Fe1<}|!ts%13H{R}!tt7Dn11nKPnPMPl!uc/z!tt%P{PFQ0WPv!#BB$R{$0!z]$1<}y!#>2%Q0W!#=v;!#B:+}zQ0W1Myz'>!#=jD!yh9aPyPzP{P[DEe!yq%X!#Dh4!yN'Q/6u!ur&8Hr,3H!us7~w11wKPwPdPM!us/rE?Q0HeQ0IQ0J1D@CQ0<CgCg40=W<Q0G#QPIPrPcPFA5occRM1=ccRw!#Mq%~=0a>R{1fLLRz'4PaP~P[PLPCA0:B;EIP{Pz!#F[$PmPfPAPFPePAPA!#FG$GpP>!#FG$:PB!sI-:Ps%me#`Q0K'2/221NuuRu!uu4!wo&!sj$3:!sj5P2P!s[Fa122;!x%'mf!xX&1Mmf!xY,3!xY4!zRE>X3:1Da>1<IIR5&06I!{G%PcPFPv!y|+u!y|'25!tT+Ir1MIr,>v!yUX>!#WN$rPuP>DEe%mo#`163I'2R3/2B&0J3E?16II&0KIE?!sS&cPFPM!v</ePw&0LcE?1D@LCg40MW<!#5v0P2O1b<b3PaQ0APlQ0FPFQ0F=5jqQ0F/=!#X?&hP>Q0BPjQ0FPkC;R>Q0CPaPhP[P>Q0DQ!#X+$ePiPkPj!#=H;UP6Q!#Pc6Q0N!#PZ+P2Pm%nk,3HPdO3!{L'Q0B#n,3H13HqRq'_RdePdeP4Pl13Hp/12XA4!#F90RQ0VP211fKRKPfPmP`!#>++11qle18Hl!|x:mfPKPfP\P`!|v/lE?13Hj,1qeH0:E?Q0@!ue$iP_H0NE?CgP=P2E?W1!s-+1P2O!#DN0!s/&W1P^!sJCb1bJbOW1WLWMWKWNbPW=X>@XI<XQ@XC4o"). Qed.

Lemma went_In_bounds : ltac2:(zQ "h90!hk3!hn3!ij9!re!ii2!ht0!il4!hi5!htf!klc!hne!m5!ig4!it4!im2!kl4!pe!lhd!ht8!hs9!jp8!jq5!jk2!kq7!s4>1L$h6>4pbrk$0>2mo$f>1b$0>1l$0>0@3$h7^5^4^3>0@2$e@3$6@2$2$0$0@4$4$0$0^3^2@1$h4^6@2$d$0\1k$0@3$6@2$2@2$2$0$0$0@4$4@2$2$0$0$0@4$4$0$0^4^3^1@1$h5^7@2$3@2$bZ^4@2$3@2$bZ@1$1^3@2$3@2$h8@2$a^4@1$1^3@1$h0@1$9^5@2$3@3$6@2$2@1$c@1$8#k0@1$c@1$8#k0@2$5^4@1$1^3@1$h1@1$9^5@2$3@3$7$0@1$h3@2$5^4@1$1^3^4@3$7$0@1$h2@2$5^4@1$1^3@2$a^4@1$1^3").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##mOp'0h01eh11qh22H1h34__p1h44__x1h56__sat3h62Hah74__p2h8!s;%5h94__x2h:2H0h;!s;%2h<!s/%4h=1kh>2H2h?2H4h@2H7hA2H8hB7__arithhC4__ffhD4__p3hE!s_%7hF8__varmaphG5__withH4__x3hI4__x4hJ3H10hK2H9hL3HinhM3H11hN2H3hO2H5hP2H6hQ!sv%6hR1HhS3H12hT3H13hU2HbhV2HchW2HlhX2HmhY1KhZ1Lh[!s[%1h\1bh]1lh^2moh_4pbrki001xp%0p&0p;3p;2p;1p;4p;7p;5p;8p;6g02?Ok30KTg01?Rj2vTg02Y9j1pTg01A8j3?Tg01:Aj4WTg02\Mj1]Tg01WUS00j27Tg01D^R0k20@Tg007_j1YTg008Dj1U!s/$bj1GTg009Gj2o!s/$dj2<Tg02C2j15Tg02N7k40JTg05=Ak20HTg00@0j1;Tg013Cj16Tg00HFj1zTg018^k10>Tg00ADS01j20Tg02X1k708Tg00XZj21Tg01;Kj2ITg02Z@j39Tg01Q1j4RTg05>Lj5KTg02[Fk80I!t@$hj23Tg01<Mj1`Tg01>Qj1_Tg02G9j1V!t?$_j2tTg00BGj3s!s/$kk20F!ur$Ej2|Tg00CLk10E!s0$lk10CTg00DLj2g!s/$jk10BTg00EHk10ATg00F3j2{!s/$Vj2fTg00Gdk10?Tg00Ikk20=Tg00JMk20<Tg00K9j3a!s/$Sk30;Tg00L2k40:!uP$ik209Tg00]ej1[Tg00^Dj2TTg00agj2bTg00c?j3e!s/$_k107Tg00d=j4dTg00fEj3x!w7$dj3yTg05@3k306Tg05A:k405Tg00Z1j2wTg00YTj2qTg02I5k104!u4$9j4}!td$dk70DTg014jk603Tg00MHk702!uQ$Gk80!y2$jUk301Tg00SjR1P1f1R2f0R3CWp=Qg00S0R4/<3p=2g00;LR5,33p=Pf2R6/02/03p=ug02oER7,<3,02p=r1162%;3'3p=H%Y3#Yp=\f3R81I62%V33?p=81023,06p=4g00oPR9,w3=a14p=O%;3,32p=i%V39?62p=k1<27,06!t=$D1<4!tG%E1186/3!s3%J1w39p=nAa124!s8$m1162/33p=>1<37p=Ff6R7f5R:f4R;P8P6P2P3CRCRp=lP:10;!s9&DKp=@1343p==1q39p>00&04;9?7:13861129/33'0'0p=:1q69!tS'C13!tj&jA?86!s1%hA9!s1'^1q!sa$p=~Aa123p=NP1P2g00U[P3C}p=Z!s4$MlR9g00NKR<P<g00NkR=P3g00OKK0Dp=BP2P9P<P<P=P3J03p=SP6!s8+2P3K02p=MP8!s:+!uO$L0Gp=A13!t\&cB01!tS$L!tS'4!tS%Xg02lJg02mNB0K;861v11R91Q62%p:3?1v91R>P9P11Q86P3CW%]73?X=1,71+0@g05BAg00<YR?#YR@#URA%G?RB#G!s$&URC'oRD,<5%5:R5f7REP7P:P6H0J+0H%;5R5#2%P5%G@!sY%S02#URF,oARG,<53uP01Q:;f8R0#p5?9!t\%7:R5P3CWf9RH#]5?>!tb%%2:RI/r:S03%27RJ%6:RK%5ERL5H7%Y@S04#\#\R@#zS05$0>RM/vMRMP7PKPLC834S06'0P6%pH9?95f:R5PHP0P:PEP7P3K08%2ERL%OE%67RK,1ES07%50RN'iS081IEKRO=kMNS09A95EK34349DJ7%5HRJ#;RN%PN'ES0:1<NG1rLES0;%20P0%6ERPPNPMP0PPPJC8CJ34S0<Q0:%55S0=#;S0>/<G%2HS0?/rHRJ%25RP%n5%6HRNf;RQ#5RR5H5RSPMP5PNPRC8RRf=RT?95N34'm10SRS0@94JP%2QRR%OQS0A%65RS,1QS0Bf<RN#5RU'iRV1IQSRW=kMURUf>RX?9QSS0C3434%5TRY#;RZ#2R[%PZS0D%2NS0E%6QR\=>NZPMPNP\PYC8349DRQS0F%5XS0G#;S0H#P%2TRY%FTR\10Y\S0I%2XS0J%6TR\f?R]#5R^5HXS0KPMPXP\P^C8S0L'034S0M%FXf@R^#2R_%O^%6]R`fARa#5Rb#;Rc5>^RdPMP^P`PbC8RbfCRe?9^`34%2]RfA4_db7D]S0N%naPa%6^RbfBRg#5Rh#;S0OPMPaPbPhC8S0PfDRh?9ab'0CJ'm%OgRi%6aRj%5eS0Q5HgRkPMPgPjQ0QC8RlfERm?9gj'0%2aS0R%FaS0S10kl,Eg3uS0T%6gRl,1eS0U%5hRk'iS0V1IelRn=kMkS0WfFRo?9el34%6eRp%5mRq5HhRrPMPhPpPqC8RqfGRs?9hpS0X%2eS0Y%2hRt?4rq7DeS0ZPMPm%6hRu%5oS0[C8S0\fHRv?9muS0]'0PMPo%6mRw%5sRxC8RyfIRz?9owS0^%2mAHowxS0_/0y,Eo7DmS0`fJRx%6oR{79sS0a%2sS0b%FsS0c'0S0d%2vS0e%6sR|%5zS0f5HvR}PMPvP|Q0fC8R~'0S0g'0S0hQ0bQ0cPHP0CRQ0eQ0gPEP}P~P8P2CRFlWJXAyP3DKWKX@rP3E@WAX?i!s/$@X:_P;E@WPX>YP8DKWOX2[!s/$?X:JP6E@WNW>P8DKb2WLP3O1!#3D$E7!#4z$5!#3?'Q00P!sC&0E!sC%Q!sC%Q0<P3!s@%5H!s@%T5?>PXPTPNPHPQP5!#6q$IQ0A%=2%U?R>/12Q0CA>>63112>$00R9%6NS0<'3PMP3%5^RJ%`3RY&008R_,1]RiPi%_3RiF:X0M,7M[[^1154U7CS54V54R9DP5Q0D,0[S0D1<ZGQ0FQ0DQ0H/<GQ0IQ0J%nXQ0K%=;11>;Q0LA9aX\11>:RZ/33139`PMP3Q0QPY11g_R`P`P!t?1347C\34'mQ0MQ0I%O]%6XR\,1]S0M/iJS0Q%=:S0J1I]\R`=kMJS0FA9g]\A>>73139bPMP3PkPY11e_RkPk!t149CZ\3454f%2cS0A%PcQ0NQ0AQ0O#PQ0RQ0SQ0TQ0R%FgPt%Oh%=511>5Q0X11>QRc!uC%w!uC%fPY11v_RZPZ!t8254q7Cp54rQ0Z%nmPmPuQ0[#;Q0\Q0]11>NRr!sq%{!w\%xRpPY11z_RqPq!u,6cu,jQ!~b%oS0]Q0_Q0^11>T!ta'|PMP3fKRu#5RqPY11x!tf9y9Crw,jNQ0`Q0]PsP{%5vRr#;PM1Is{%VrQ0a11>X!to$%6vRw,39!t'$LRy#5RZPY11u!v}7'0Ch9Cc{,jTCJP}%=XA9uv|11>]!tt$%6zR{!ss'MRk#5RbPY11y_RJPJ!tx4~9Cr|Q0dQ0h'0PM1Izw%VpPyPzPw11>^Rp!sz$xRr!sz'NR|#5R~PY11k!sz7C^!to$w,j]%=^S0h1~p{PMPxP{PqC8S0dA9kx{11>a!t'&uRc!t''ORw#5RJPY11|_R[P[!wl4%2z%FzS0aPxP{%;qQ0dCJ,Ex3uQ0hPM1Iur%VZP|PuPr11>gRg!t2$yRZ!t2'PRx#5PY11w!xv7!u5%pr1~gcRgPMPyPcPb!u-$PwPyPcA>>e3%6kRp!sw'QRr!x~-!u'5C^%2uPyPc%;b!t}&y7DuPM1IkZ%V~PxPkPZA>>h3%6|S0d!t#'RRu!tx%r_RbPb!tx6PMP|PpPJC8RbA9r|pA>>m3%6wRm!sk'SRc#5R[!yg%S0`Q0!~s3%2kP|Pp%;JPbCJ,E|7DkPuPwQ0dA>>o3%6x!ss'TRo!t`%c_R|P|!t`4A9cxmRcA>>s3%6rRs!s_'UR|!s_%o_RoPo!tP4wPxPm%;q!y?$mPqC8!xD$7DwA>>v3%6u!sp'V!sn%|!tO7%2rRi%FrRr'0%2uR|AHus[R_PMPuPsP[C8R['0Rs'0PiPrP]PXCRP|PsPTP_P[PHP8CRFlWTXMcP3DKWSXJbP3E@WMXKg!s/$JWA!s-$KX@}!s/$AW?!#:L&t!#:L$!#:1$WOW2!s-$?W:!#:I'E!#:I$X=1P2P3O2n20010!s#$121!s0%W2P3O1!s@-!s?%!s'$%2;%6;Rt%57R}5H:PMP:PtP}C854I7D;Q01Q03Q06%2KQ08Q09%`O/NE%_OQ07'N'03454LP3Q0;Q0?%60RLQ0>5>HPMPHPLQ0=C834Q01PPQ0@%2S%`W/NQ%_WQ0B'N'094VU54RP3Q0EPTQ0<Q0HPM!s0&GC8CJ!tR$KQ0L%2\Q0QQ0F%``/N]%_`Q0M!tR'fP3Q0P1tACRf%2AR`%=C%2D[R][R\%=ARTg00SNRMAsAC2UW6RC%=D\M^6TRD1tAFRR%=F%2G[RU\`RVAsAF2VMX6TRF%=G!sO%WP2g00:@20F4A'|P`eRQO1RSPUP;PQO1RPP]p-0RLg00THRH$0ERO&0CHRK1g12&0B1R}&0A1Rt1{14Rg1f1?R?'Z,BtRb1St85Mt&0?<R<PbCA20=t=R=P3P6g00VBRcg00VbR['|20<36=ac[dB0;142H0:R4bCbFbGX41W31E32%22[^41^3LP3%FvPvP^O3bBb<b;b[b;b5b<-09a%\@#\#\#UR[,1a,<j9cajQ0Y%2lRjQ0VQ0W%`n/NeRc%_nQ0U'NRn'0R_!{_%R|'0P7PjP|PfP\PCPDPRPVPFPWPSPUPPP]g00l]R|#[Rj#[RX,T1Rr1T1j1T1|R|'LRj'LRig00m<Ru'b=eHOPKP1P11g16RYP6&071R9CdP2P9CdP}PtQ04,f1R9/X?,BtR>1St;5MtP<Pt1Zg9,BtRw1St:!s:%bCACAP=P!v?,X91X3LX7LAc236%26Rx/0;Px[!vO$91^3L^7!{=$a11z[,<{PzP{PEPaO6bBb8b5!v^%b8Q0VPsP6Q0WP_P2PcPn!u}3%U@R@,tARn%=@1oA@Rc#2[R_\`R`AsA@!y|&@%=c!y|%TPSP_PPPUPE!yk$QP]%[XRX#[RM#[,T1Rs1T1MRM/Li'L/bu!vP08P;1g1;!vL$YCdRYP}Pt%YB,f1Ri,X9,Bt1St7R7!vN&Ax1?i1f1BRB'X,B!s:$Pb!vh$StE9Mtw!s2&01{1ARAQ02#z5y1,ZB,Bt!sk$1Xg?,BtQ059y1A,Z?!s?%CACARACA!wD8H1XI!wJ&XDLAc68;A>2;610I01<:G,05Q0J1<:c'0[[Rc\!wb,H1^I!wh&^DLP3%;~R~%P~'ERx%FyR:11y[,<ZR[PZPyP~PkP5PNP^PhPvO<bBbE!x//bQbERG:06elPePlPG!{,4nP`P@P!w\,QP]1T1X/Lj,LM/bu1Lr|,Ls!wO&5eHPKP!w<$AMt>7!w&&i?/XB!v}&1Zgi!s1%!v<L3;A>;26Pc\I!u~<PxP:P[Pk!uj$Z!ujCH05CRFlFlb2WXXVd!#976!s/%W2WU!sD@W!sD=b2b:bRWLWYX]1X\1W^X_1WZo"). Qed.

Lemma In_lranges : ltac2:(zQ "h40!hk3!ij9!ii2!it4!hi5!il4!re!im2!hm6!jn8!ll2!jka!jl4!jp8!jq5!qm8!qn3!jk2!hne!jjc>1L$h1>1x@2$1$0$0>0@3$5@2$1$0$0^1@1$h0^2@2$7@3$5@2$1$0$0^2@1$f^3@2$7@2$3$0\1b$0@2$3$0\1l$0@2$6@3$5@2$1$0$0@4$2$0$0^2^1@1$d^5@3$4@2$1$0$0^4@4$2$0$0^2@1$8^1@2$7@2$3$0\1b$0@2$3$0\1l$0@2$3$0\1k$0@2$6@3$5@2$1@2$1$0$0$0@4$2@2$1$0$0$0@4$2$0$0^3^2^1@1$e^6@3$4@2$1$0$0^5@4$2$0$0^3@1$8^2@2$3$0\1b$0@2$3$0\1l$0@2$6@3$4@1$b@2$1$0$0@1$c^5@2$a@2$1$0$0@4$2$0$0^2^1@3$4@2$1$0$0^4@4$2$0$0@2$h2^2$9@2$h3@1$8^1$9").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##\2p'0h01li001lh11bi011bh21kh31Hh41xi021xh52H0h63Hinh71Bh85lemmah91Ah:1fh;1pi031ph<2x0h=1yh>1Lh?1gh@1mhA1oi041ohB1zi051zp;2p;1p;3p;4p;8p;7p;;p;5p;6g01?RR0j2eTg05CPj1tTg01A8j31Tg02K5j1PTg02Y9j15Tg02>Tj46Tg02\Mj12Tg00Clj1aTg02`Aj19Tg00hLj1@!sA$Lj1rTg00c?j3qTg01FZj3?Tg05DUR1j2XTg01D^R2j27!s<$nR3j3lTg05E_j4WTg05F>j4R!s/$ej2jTg05GRj8bTg05HEj7hTg05I4j3g!s/$jl;_Tg02AYR4j1fTg02aHj2HTg01Cjj3]Tg01WUR5j2GTg05Jej5sTg007Ej2UTg01Q1j4Z!u|$Oj6Y!to$Dj3LTg00K9j38Tg00Gdj1pTg01>4j3cTg005dj3\Tg01:Aj4MTg00XZj2oTg00W_j2nTg05KDj4mTg00ADR6j2NTg01YGj4kTg00SjR7f0R87c7#@p=CP7P7f1R99\77P8CMp=FA\978p==g00oPR:,o8p=I1n8:p=OP7P7P9!sO%3f3R:f2R;;19/78p=<p-0R<P<P1P1P8P1g05L7R=P3Gbp=i%P891;9p=K!sH$9P8Cmp=VP<f7R3P1f6R>P2f5R?f4R@P:P;P9P8M;_p=`!s4'C691?@p=D1798,7;p=^A1?@:A8;98'Np=41G78p=0P;!tu,;A8!sI/B1G7!t}%A!s?%1!s?&>%5!to&TA8:;9/N8p=J!s^$,N:p=[P7P7A\77;Ac779#@CM=8:8p=:A1!sU'QP7!tx&kp=E!vK%%@!tU$d!s4$;P9!s]'Sg02lJ1e77RA%t991A8%P;RBPAPA%C8,F8RCX?ARD%5;C61eA7REPA1=A8RF%CF'FRFX@ERG%2;C6P4PA%aARH%9;P0!t9$HP8%I9%@8RI#ORJ'3RK%rARL5qARMn2001103000120101100RNPLn!s1$2000210!sF$5?A5?ARO5?A91A9PAP9PBA1A9OC<RP'X%P:RQPAPAPD%5:C6RRPEPAPG%2:!te%PH%9:P!t&;RS5?ART!t+%;A1A;QRQA1A;TRT'7;l8W8PAPBPOP9CWP8O2PPPAP;PRA1A;SC<RP,XTP<^7<RTP!z:%=CRR=PT\<P<P<\<P1!s>&1CRROCRP2g05LURBP<PT!sU%g00OK!s5&11j<1RUPOP=%iUGbFhRUAKA:@RVg05MF9g<1RW/VV!uj'@C6RX!uj'@C6RY!ul'@!ul9RZ5?AR[!ui%:A1A:XRXA1A:[R['7P8G`!uj$RPSP;!uj%17QPPAP:PYA1A:Z!ul%[PTP=PUAKA@?RU1VWUPAP@!td'?EDR=!td'?C6R[!td'?!td:Q!t_%@RS'7!sp$[A1A@QC<RQ,7=R[!v>&OP2PBP=1VW=PSPQ!}Y$!u$&YPZP:!u$%A^VXPP2PUP[AKA?>R[PA1398RUf8RP#5RXPAP3139IRVE4X07#0X17#0PE13;9RZ=;A8RYf9RQ#2RSPAPP%@9R=,3;RWE4X27#0!s['%fARB%9PRO1HAUR1PAP3PKEB!s{,'A3^P8AKA>3PAPU%5QPAPPP!tG-PEPYf:RT#2R<PAPQP!t33PB%9QRRP1!s`$!t+2'A;]8X3[P8O1PAP?!wJ'>C6!s5$!wL&>!{v,>!wJ991A?C<C<P2PAP>!sm'3ED!s5$!sm&3!sm,3!sm<>C<PAP3%!|<$U%5TR[!uN$!uj3;R\#2PAPT!uh8TR]!uh$Q!uh5C<P8!w0$!ts$PXEDAKAPQ!t<%\!xM$T!t</#0R^!t@$<R_#2R`PAP\!tB8\Ra!tB$T!tB3Rb'7g05N6Rcp4p710RdP!s0$210RcP9\9Re%a;RfP6P:P8P!#9:%EDP?P@!wa$;P>P8P:E>X4?,G?[Rg!sK$8O1P9P?P8P;E>X4@,G@P@!s8$!si$EDRh[P>P?!sO$:P3P8P@E>X4>,G>\h!t6'P8DsP9n20010!s#$12!s-%0X=;W0W:W7W9RhPg^=;^0f^:e^7c^9dRd!vg$APDP[PQP9O6PAPCPTPAP8PXE>X4A,GAP5!sJ$CP\PAP8%5_R!sA%PAPUf>R[#5PAf=RD!w91P8!#8Z%APCP[f?RC9TA8CJfBRc9TAURePAfARfPVC[!s\,[P8PA%CU,FUPfPeCJP6PAPZPZPcC:fCRe9TAZ!tG$F#5RZPAfERg!tG4A13@:RiPifDRjC:PA13?@Rk%Ck'F13>?RlfGRm5TARn!sr$JRo#5PAP:!sp1[X4AA1Ak!t?%IRZ#5PA13P3RpPpPVC:CQ!yT+A1338fHRq!sJ%3>RrPr133I!sL&PnPAPlPl%@?Rn,3>RIC:P81UAICZ7E?7E>W3PgP8EYW5P9P8O2!x=0!s/&W5X07X17!sH-!#<7&1105105X<A!se7!}[%b3b59]^b3LW3!#37%3!~9'P!~9'PO!~8<3!~}&P!s[%PSED!sZ&R!sZ<PPAPQ%!yj$UPX!}1$!~g2%2D!}j$_!}J8_!}H$\!~d<Q!tZ&<!~d$T\R<!~f%D!sx$!~d1V!t=%[RU!{Z$!t=3#0RRPB%9D!tA$_!tA1RS'7RO'7RbPhPdP8!tE&`P\!|F&FP_PE!|F'E,GEP5!sJ$FPD!s>$U!s>$!tP%fRUPAf@R!tR7!|G$A!|G$!sa-!s^%g!u0$j!s\6[!|~,A;A98RD,=A!#C3%PjPEPD!sl,ZRZPAPq!sl7^B7!|N$=AYRU%CU'FPm!s[%qE>P6PA13:;=;A9R6,=ARUPUPqC:A1E6ZPEPYfM#2R6PAfLRZ!uQ9AA;Ak:,=ARqPqPoC:!s8$l@Ro!s:$%Cq'FA;Ar?Rq=1E6R6!s}$Q#2PAP@!u$7X4A%2Z91Eo!sP$P#2PA13TQ=;AP,=ARTPTPW!};$!yp0E13Q9=;A8fO!sX%QP=;A3,=ARWPW13Q=!sZ/PEA;Ap8fN#2!t~$p>,=ARpPp1dP3!sO&!v<$=AqRqPq1d3>Rq!~@&q!~@'7E3W3fK!~CF27!~FD;A!sC93!~c$E!~cCRS9LVO!~g+!}|%]!}|<QPaPB!sL$!sP%8!sP<_PBP:P1A8ACKRCCJ!wq,]3!zb'A1A[NPB1HA:!|y$f!|y1]3P8A1AfMP2PA%I;%O=PcCSA1AcL!s\$kRk!s^$g!s^1P8PA%I:%@;#OPeCSPA%I@%@:#O'3Rg1HAr=8B1RrPAP;PK!#9m-X4A!t#$lP1PA%I>%OnPKCS!u4,PBPk13?8,HAPA%I?R?%@@#O13?J!sM&1HAiRi=8BiA8Agg1UBi1UAgCZ7E:7E@Pj!xe$!w4$A1AeLg00mhRePrPAPm!t\1P8n!w|'0!sX%!x6-2110!s3&W3!y<G!t?%\LPePB%pAP1P!w\0!t;1!xA%4!t6%!ss$P9O1bA9L!yG%9L<b!ta;1!zz$!sBP0!sB'b6b6b6W6W4W>o"). Qed.

Lemma KLB_lbrk_pages_ok : ltac2:(zQ "he0!hk3!hi5!htf!hne!ij9!s4!ina!io2!jn8!m5!nr6!ig4!ll2!ip8!jka!ii2!re!im2!kl4!s9!pe!klc!ioa!lhd!lj5!qne!jl4!jk2!kq7!ho4>1L$hb>4pbrk$0>2mo$h2>2lo$0>3len$0>0@3$hc^5^4^3=1h$h3@1$h5^4>0@2$9Z^4>0@2$9Z^4>0@2$5@2$3^6^5@1$h4^3>0@3$1$6@3$h6@3$d@2$4@1$b@1$2#k0@1$b@1$2#k0@1$h8^4@1$h7^4@2$a@1$2#k0^7@2$a@1$2#k0^6$7>0>1b$0>1l$0>0@3$1@1$e@2$4$0$0@1$ha^d@2$c@2$4$0$0@4$f$0$0^2^1@2$h0@3$1$0@2$hd^2$8Z@2$h1@2$5@2$3^3^2^b@2$5@2$3^b^a@2$3^3$8@3$1$6@3$h9^c^9^8$7").
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is
   untouched, so no caller changes.  CAUSE, from a farm round
   (the source branch) at this line: the replay
   consumes [kb_resv] as the old plain equation, and this commit weakened it to
   the prefix existential for the vDSO suffix.
   PROVENANCE, cited BY BRANCH, read per hunk with git show:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/Spec/KLink.v
         -> KLB_lbrk_pages_ok, the plain-text twin in the other tree of the
            fork, whose [kb_resv] is already the prefix existential, so its
            [(rlo & rhi & Hrlo & Hlr)] opening is the one this tree now needs.
   The donor carries no address and no constant, so none was taken from it. *)
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl. pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [Htop _]. fold h in Htop.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - destruct (kb_resv _ _ _ HK) as (rlo & rhi & Hrlo & Hlr). rewrite Hlr in H. destruct H as [E|H].
    { unfold rband in E. injection E as <- <-. left. exact Hceil. }
    apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    assert (H' : In (e, sz) (vm_reserved h)) by (unfold h; rewrite Hrlo; apply in_or_app; left; exact H).
    pose proof (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H'))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite <- mmap_len_round_up. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite <- mmap_len_round_up. exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.

Lemma with_vmmaps_vmmaps : ltac2:(zQ "50!s9!hi5!kl4!klc!lvb>2hh$0>1m$2@3$1$0@1$3@2$4^2^1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["HC"] "h02hhh11mp;2g007Ej20Tg00OkR0g02mNf1,00W1W0o"). Qed.

Lemma ev_brk_grow1_ok : ltac2:(zQ "i10!mk5!hk3!pq2!re!oq4!ohf!mm1!hi5!kl4!jn8!pnc!s4!jne!pr4!ov4!okd!jm1!jme!jk2!njd!kq7!pg9!ph9!pm3!pmc!hm6!pn2!qof!qp4!po4!poc!pp4!hne>1L$h2>1G>0$0>0$8P>2s0$0>3cur$1>2cb$1>2ck$1>0@1$h6^5>0@3$7$h0@1$h1^7@1$f^4=3req$1@2$i0@1$h9^5@2$c+2$9>0@2$b@2$c+2$9^5>0@2$b+1^5@6$h7$ha$0$1\1s$0\2mo$8@2$3@3$7$0^2^b@2$3@3$h4^d@1$5^2^1@2$3@2^c^2^1@4$h3^d^1^9^8@5$4$0$0$1@1$hc$0\1s$0@5$4$0$2$1@4$hd$0$2@1$e^4@2$d@1$5^1^4\1a$2M2\1a$2@2$hb$0$1^1@5$4$0$6$1@2$he$0@1$hf^5\0$6@3$a$0$1^6@3$a$0$1@1$5^2@6$h5^b@1$h8^3^a^9^7^6").
Proof.
  intros L G s0 cur cb ck HG Hph req Hcb Hck. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KLB (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                              /\ BUD (set_brkph (BPGuard cur) L) mo (cb - 2 * PGSZ) (ck - 1)
                | BrkSame => KLB (set_brkph BPDead L) cur mo /\ BUD (set_brkph BPDead L) mo (cb - 2 * PGSZ) (ck - 1)
                end)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    split. { cbn. unfold PGSZ in *. lia. }
    intros rsp mo' evs Hst.
    destruct (nstep_dec_brk' req mo rsp mo' evs MI ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as [-> [[Hdec ->]|(Hdec & -> & Hgo)]].
    - (* [comment removed for export] *)
      exists BrkSame. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz req)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HK' : KLB L cur (with_vmmaps h' mo)).
      { rewrite <- Epbrk. eapply KLB_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)| ..];
          rewrite ?with_vmmaps_vmmaps; first [assumption | reflexivity]. }
      destruct (lbrk_dead L ltac:(right; eexists; exact Hph)) as [D1 D2].
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + eapply KLB_rephase; [exact HK'| exact I| exact D1| exact D2].
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount in *. rewrite D1, D2. cbn [ld_groups ld_metas set_brkph]. rewrite with_vmmaps_vmmaps, Q6. splits; try lia.
    - (* [comment removed for export] *)
      exists BrkGrown. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      apply brk_grow_ok_facts in Hgo; [| lia| unfold PGSZ in *; lia| rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      pose proof (brk_model_next_grown (m_vmmaps mo) req ltac:(lia) ltac:(unfold PGSZ in *; lia)
                    ltac:(rewrite Ebrk, Ecur; exact S2)
                    ltac:(rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity))
        as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KLB_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk (m_vmmaps mo))) at 1 by exact Ebrk.
        replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) by (f_equal; lia). exact Hrf. }
      assert (Hn : bv_unsigned (MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = 2 * PGSZ) by (unfold MmNodes.wz; rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0. unfold bv_modulus in R0.
      (* the two vDSO fields, proved before the [constructor] so that the shared
         bullet tactic below never sees them *)
      assert (Hvdi : incl (vdso_reserved (m_kernel (with_vmmaps h' mo)) (vdso_top (m_vmmaps (with_vmmaps h' mo))))
                          (vm_reserved (m_vmmaps (with_vmmaps h' mo)))).
      { apply (kb_vdso_in_eq mo); rewrite ?with_vmmaps_vmmaps;
          first [reflexivity | assumption | exact (kb_vdso_in _ _ _ HK)]. }
      assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps (with_vmmaps h' mo))) ->
                       forall e, In e (vm_maps (m_vmmaps (with_vmmaps h' mo))) -> edisj e r).
      { rewrite with_vmmaps_vmmaps, P1, P2. apply kb_vdso_disj_cons; [| exact (kb_vdso_disj _ _ _ HK)].
        rewrite Z_to_bv_bv_unsigned in Hrf. exact Hrf. }
      assert (HK' : KLB (set_brkph (BPGuard cur) L) req (with_vmmaps h' mo)).
      { kb_open HK. constructor; try exact Kresv; try exact Krtop; try exact Hvdi; try exact Hvdd; try exact Krdr;
          rewrite ?with_vmmaps_vmmaps; cbn [set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
          rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7; auto.
        + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; rewrite Z_to_bv_bv_unsigned in Hrf; exact Hrf].
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
        + intros b l Hin. specialize (Kgrp b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
        + intros b l k Hin. specialize (Kmet b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
        + intros b l Hb. rewrite Ereg in Hb. discriminate.
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
          * exists (vm_brk (m_vmmaps mo), MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
          * intros b l Hin. pose proof (went_In_bounds _ _ _ b l HK (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
            rewrite Z_to_bv_bv_unsigned in Hrf.
            pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
          * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
            rewrite Z_to_bv_bv_unsigned in Hrf.
            pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        + unfold vm_live_bytes in *. subst h'. rewrite P2, live_bytes_cons, Hn, Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg set_brkph ld_groups ld_metas]. rewrite Hph, Ereg. lia.
        + cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg set_brkph ld_groups ld_metas]. rewrite Hph, Ereg. lia. }
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *. cbn. rewrite Hph, Ereg in B2, B4.
        rewrite with_vmmaps_vmmaps, P6. splits; try lia. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & (HK & HPG & HB)). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK & HB). unfold ev_step_post.
    cbn [answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

Lemma ev_brk_grow2_ok : ltac2:(zQ "i50!hk3!mk5!pq2!re!hi5!oq4!ohf!ij9!mm1!kl4!jn8!pnc!hne!s4!ll2!jka!ii2!pr4!ov4!qpc!jm1!jme!jl4!jk2!njd!kq7!pg9!ph9!pm3!pmc!pn2!qof!qp4!po4!poc!pp4!jne>1L$h7>1G>0$1>0$9P>2s0$1>1b$0>1l$0>2cb$0>2ck$0>0@1$hb^6>0@3$4$h4@1$h5^8$h3>0@3$4@1$f@2$7$0$0@1$h6^9@2$e@2$7$0$0@4$h0$0$0^6^5=3req$0@2$c@2$c^7^6$a>0@2$d@2$i4+2$a^6>0@2$d+1^6@6$hc$he$1$0\1s$1\2mo$9@2$3@3$4$1^2^d@2$3@3$h9^f@1$6^2^1@2$3@2^e^2^1@4$h8^f^1^a^9@5$5$1$1$0@1$i0$1\1s$1@5$5$1$2$0@4$i1$1$2@1$h2^4@2$h1@1$6^1^4\1a$2M2\1a$2@2$hf$1$0^1@5$5$1$8$0@2$i2$1@1$i3^5\0$8@3$b$1$0^6@3$b$1$0@1$6^2@6$ha^d@1$hd^3^c^b^8^7").
Proof.
  intros L G s0 b l cb ck HG Hph Ereg req Hcb Hck. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KLB (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                              /\ BUD (set_brkreg (Some (b, l + PGSZ)) L) mo (cb - 2 * PGSZ) (ck - 1)
                | BrkSame => KLB (set_brkph BPDead L) (b + l) mo /\ BUD (set_brkph BPDead L) mo (cb - 2 * PGSZ) (ck - 1)
                end)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kb_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    split. { cbn. unfold PGSZ in *. lia. }
    intros rsp mo' evs Hst.
    destruct (nstep_dec_brk' req mo rsp mo' evs MI ltac:((first [clear - S3 S1; lia | lia])) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as [-> [[Hdec ->]|(Hdec & -> & Hgo)]].
    - (* [comment removed for export] *)
      exists BrkSame. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      pose proof (brk_model_next_noop (m_vmmaps mo) (MmNodes.wz req)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HK' : KLB L (b + l) (with_vmmaps h' mo)).
      { rewrite <- Epbrk. eapply KLB_vm_eq'; [exact HK| apply mminv_with_vmmaps; exact MI| rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)| ..];
          rewrite ?with_vmmaps_vmmaps; first [assumption | reflexivity]. }
      destruct (lbrk_dead L ltac:(left; unfold brk_quiet; rewrite Hph; exact I)) as [D1 D2].
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + eapply KLB_rephase; [exact HK'| exact I| exact D1| exact D2].
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount in *. rewrite D1, D2. cbn [ld_groups ld_metas set_brkph]. rewrite with_vmmaps_vmmaps, Q6. splits; try (first [clear - Hcb Hck S2 B2 B3 B4; lia | lia]).
    - (* [comment removed for export] *)
      exists BrkGrown. rewrite Ebrk in Hdec. rewrite Epbrk. split; [exact Hdec|].
      apply brk_grow_ok_facts in Hgo; [| (first [clear - S3 S1; lia | lia])| unfold PGSZ in *; lia| rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      destruct Hgo as [Hceil Hrf].
      pose proof (brk_model_next_grown (m_vmmaps mo) req ltac:((first [clear - S3 S1; lia | lia])) ltac:(unfold PGSZ in *; lia)
                    ltac:(rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity)
                    ltac:(subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity))
        as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
      set (h' := brk_model_next _ _ _) in *.
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KLB_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [(first [clear - R4 R3 R1; lia | lia])| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk (m_vmmaps mo))) at 1 by exact Ebrk.
          replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk (m_vmmaps mo)))) by (f_equal; (first [clear - Ebrk; lia | lia])). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      assert (Hn : bv_unsigned (MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))) = PGSZ) by (unfold MmNodes.wz; rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (bv_unsigned_in_range 64 (vm_brk (m_vmmaps mo))) as R0. unfold bv_modulus in R0.
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hvdi : incl (vdso_reserved (m_kernel (with_vmmaps h' mo)) (vdso_top (m_vmmaps (with_vmmaps h' mo))))
                          (vm_reserved (m_vmmaps (with_vmmaps h' mo)))).
      { apply (kb_vdso_in_eq mo); rewrite ?with_vmmaps_vmmaps;
          first [reflexivity | assumption | exact (kb_vdso_in _ _ _ HK)]. }
      assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps (with_vmmaps h' mo))) ->
                       forall e, In e (vm_maps (m_vmmaps (with_vmmaps h' mo))) -> edisj e r).
      { rewrite with_vmmaps_vmmaps, P1, P2. apply kb_vdso_disj_cons;
          [exact Hrf | exact (kb_vdso_disj _ _ _ HK)]. }
      assert (HK' : KLB (set_brkreg (Some (b, l + PGSZ)) L) req (with_vmmaps h' mo)).
      { kb_open HK. constructor; try exact Kresv; try exact Krtop; try exact Hvdi; try exact Hvdd; try exact Krdr;
          rewrite ?with_vmmaps_vmmaps; cbn [set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live];
          rewrite ?P1, ?P2, ?P3, ?P4, ?P5, ?P6, ?P7; auto.
        + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
        + unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try (first [clear - Kstart Ebrk; lia | lia]); auto.
        + intros b0 l0 Hin. pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
          specialize (Kgrp b0 l0 Hin). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
          unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
        + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
          specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
          unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
        + intros b1 l1 E. injection E as <- <-. splits; auto.
          * clear -R3. unfold PGSZ in *; lia.
          * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
          * clear -Hceil. subst req. lia.
          * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
            -- destruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
            -- exists (vm_brk (m_vmmaps mo), MmNodes.wz (req - bv_unsigned (vm_brk (m_vmmaps mo)))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. (first [clear - Hge Hx Ebrk; lia | lia]).
        + rewrite Hph. exists b, (l + PGSZ). unfold MmNodes.wz. rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; (first [clear; lia | lia]).
        + unfold vm_live_bytes in *. subst h'. rewrite P2, live_bytes_cons, Hn, Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas]. rewrite Hph, Ereg. lia.
        + cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas]. rewrite Hph, Ereg.
          unfold PGSZ in *. replace (l + 4096) with (l + 1 * 4096) by lia. rewrite Z.div_add by lia. lia. }
      splits; auto.
      + eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs].
      + unfold PGSZ in *; lia. + unfold PGSZ in *; lia.
      + destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD, ltotal, lcount, lbrk_bytes, lbrk_cnt in *. cbn [ld_brk ld_brkreg set_brkreg ld_groups ld_metas] in *. rewrite Hph, Ereg in B2, B4. rewrite Hph.
        rewrite with_vmmaps_vmmaps, P6. unfold PGSZ in *. replace (l + 4096) with (l + 1 * 4096) by lia. rewrite Z.div_add by lia. splits; try lia. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    intros s mo (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & (HK & HPG & HB)). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. intros s mo (-> & HGs & [Hne Hpos] & Ecur & HK & HB). unfold ev_step_post.
    cbn [answer_ok event_post ans_cont ev_costb ev_costk].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wcov_rf_disj : ltac2:(zQ "f0!htf!ig4!iia!hk3!s4!m5!ina!ila!ij9!io2!hi5!im2!ioa!iv7!hne>4maps@1$7@2$8@1$1@1$0#k0@1$1@1$0#k0>2lo$3>2hi$3>2aw@1$1@1$0#k0>2nw@1$1@1$0#k0>0@3$d^5^4^3>0@3$a$6@3$c^6^3^2$9>0@2$5Z@2$2@1$0#k0^3>0@2$5^7^6@2$b@2$4@2$e@2$2@1$0#k0^6@2$2@1$0#k0^5^8@2$4^7@2$2@1$0#k0^6").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##Cpp'0h04__p1h14__x1h24__x2h34__x3h44__x4h51eh61Hh72H3h87__arithh94__ffh:4__p2h;8__varmaph<5__with=4__x5h>4__x6h?1li001lh@1si011shA2z3hB2H1hC2H2hD2HchE2HehF3HlhhG2HnhH2HrhI3HrfhJ2awhK2hihL2lohM4mapshN2nwi021gi031xp;1p;2p;3p;4p;6p;7p;8g007_j1<Tg00HFj1wTg018^j1bTg01?Rj2[Tg00Clj1VTg01eKj3uTg01HNj3fTg00K9j3KTg01:aj20Tg009dj23Tg00XZj27Tg066ej2RTg00@hj21Tg067Lj2;Tg0653R0j2WTg01D^j26Tg01Cjj3t!s8$Dj3oTg01[Zj28Tg01b7j2UTg00]ej1>Tg00`?j1^!s/$]j2]Tg00a>j3TTg00^Dj2S!u5$Lj1\Tg00DLj2CTg00c_j1ZTg00d=j4A!sA$jj1YTg00EHj1XTg00FVj2QTg008bj1PTg00Gdj1v!s/$9j4JTg00Ikj2sTg007Ej2qTg00JMj2n!v7$Sj3kTg00L2j4hTg01A8j3ITg01<Mj1HTg01>Qj1DTg00ADR1j2FTg01WUR2j2eTg01N\j6gTg00fEj3d!tb$3j2i!sr$kj2jTg00jUj3c!um$gj2l!uR$?j3mTg014jj6a!tP$dj7`Tg00MHj7pTg01EZj7_!u7$Gj8rTf2R3g00SjR4f1R5f0R63K'Fp=GAK456p=O1135/F6p=51S46p=?Ac!s?$4g00THR7g00m<,l5;m6p=9P5g00MlR8g00NKR9P9g00NkR:P6Eap=M1Q46p=@P4!sO$k>P6CJp=LP5P8P9P9P:P6g00OKF`p=2P3!s<+5P6Fpp==!s_&U4!s_%B!sI2_p=N!sI'[!sI%Ef3R;!sK+3P5P6Grp=:g00<YR8#<R<#<R=#<!s$&wR>#bR?/[?R@#Vf4RA?u;3g00VBRBf5RC?f35g00VbRD3Kg00S0RE10>3'3f6RF/3C10>CRG10>A'7RHf7RI'R11HI1;HI'WP010>FRH/7GRGf8RJ'11;GJ10>IRG/7HRHf9RK'1RL11JG'6P610>JRM/7Gf:RG'111KMRN;t6X?LP6O11;HK1RKM1;KM,WN!t-$KR0,1G1;G010>GRG/70f<R0'1f;RN/1GRM!t#&N!tW$f=RL'1RO110HRP;o6X?M!t%%NG16OPPK18HLRP1UHL13HL?GPL1OPH95LH'610>0f>RH'8RPP4p-0ROg00l]RN#>RG#>RM#>RQ#>RR#?RS%^8,]4RT%?QRQ5T41S4NRN'4RU'4%?MRM/4N,4Q%?GRG!s1&\7RV,9U'9'9'9%V7R7P41C43P5!s-$ARUP;%Z4CACA%Y4RW%X4RX1MXF%@<RY1Q48RZ'L,2X5=X%P<#@R<,BZ,2X1LY<!s=%5NX%v9R9PXP4%P8R8#@R[g067hR\P<CJ,2XP9PX1EZ[!s1$1BZY,2X1EY[!sg%C:C:C:1sX:R:P6P31qBD1n63=KBDdAk4E5ChRDb9b;b<X14X24X34X44W0AGA561O5;956;'61;;A133A13AC95;A[[[^14^24^34^44^0O!x#$HRHf@RB'3PHf?RHP5PBP3P;PKO8b8bAb7O2AI@6H%H6R[%D6R],3P75P'FX5@,e@P2P@AI@6B10>L/8HRL13L]55[!sG$g00mhRLP6fBR29I@!t@$fA!xR%13P!sO%P1fCR19I@5%H510>B/82R2%D5,3235PLP6fE!se$;%HA10>1R[/82RP%DA,3P35fGRPfDR]P1PCPHP5Eg10>]RH/7[%HC'1%DC/1!yw%2R2/UP132P182PRH;GP1OH295P2'6fF,0>fHR2'8P4%>R!z#$H9T4T14SM'4RM14QN,4S,4H14QG!s0%%>R#?/4M/9V!yp%P7P4!yg$;P31C4CCAP5P4PUPF1C4FCACAPWPX%@=R=/EY,2X%<8#@RW/LY!xr%1MXJ1LW=!yi+P9PXAd4=ZRJ/B<,2X%P8#@R8/B!sJ$!sG%1B<W!ya$W8!s_%P!zD$PJP\PY!z8,i4E/EZ!z;%MXK!z-%C:C:P:P!yn6X=4X>4X0OX:O1335?GA5AGFA3'617;5/1A11F;'613FI95CF17C;/;A13EAP0[[!z43=4^>4^0O^:OP6PLfJRL!w\%'1%DKP5%HKP2PL10>P!zE$APBP]O=!zI%b6WHWEP5P6O2n20010!s#$12!s/&W6X5@!sE7103000b5'jWCP6O1!sD$1!sG$2!s,$11102b@WB!sD@FWGWIWDXN?XJ?XK4XL4WMo"). Qed.

Lemma mmap_len_pos_pg : ltac2:(zQ "50!hk3!hn3!jn8!s4!m5>1l$0>0@2$4Z^1@2$3$2@1$1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##8%h02H2h14__p1h24__x1h34__x2h44__x3h54__x4h61Hh72H0h82H1h92H3h:2H4h;2H5h<2Hlh=7__arithh>4__ffh?8__varmaph@5__withA1lhB1qhC1rp;2p;1p;3p;4p;6p;7p;8g009dj21Tg05>ij2jTg013Cj10Tg00@hj22Tg007_j1>Tg008Dj1XTg00XZj2<Tg00ADj27Tg068Oj1PTg00Z1j23!s/$Qj2JTg00[2j1iTg00Y7j2A!s/$Tj2ITg00K9j3:!sJ$Kj2ZTg00\2j2Y!s/$Yj2WTg00]?j2VTg00Bkj2U!t^$Ej2FTg00`?j1R!s/$]j2Q!sS$ej1;Tg00^Dj25Tg00a>j3E!s/$gj2OTg00bSj2CTg00CLj1MTg00c?j3L!s8$lj1NTg00DLj2D!sA$_j1KTg00d=j4H!sA$jj1STg00EHj1TTg00F3j2G!sJ$[j6hTg00Gdj1g!sA$Vj2?Tg00ebj3f!vb$bj1^Tg00fEj3]!sS$9j4@Tg014jj6\Tg00MHj7[Tg00Ikj2_Tg00JMj2`!vP$Sj3aTg00L2j4bTg00jUj3c!s8$dj7d!s\$Gj8eTf0R0#>#>p=8g00SjR1g00S0R27:0p==f1R3=c10p=6P1P3g00k>P0C@p=B!s4$MlR4g00NKR5P5g00NkR6P0g00OKFdp=4f3R7P4P5P5P6f2R8P3P0Gep=911201j30%03R9,23g00<YR:#>R;#>R<#8!s$+XR=,<3,19'7%P8%08/3=#=%07R9/J=%==R>#if4R?#0R@1A@=,I=13@='<5:1[1Z@=112=R@f5RA#0RB/3=RC,2211C='7[1YB=11=2f6RB#0RC/3=RD,1=12D2'7[1WC=f7!s?$A=#=\>1VC=f8RC#0RD/3==:1D\>1AD=P1f9RD#0/3=P1PAg00:@1U2='FP@eO11220110='7p-0R@g00THRA%R:,Q1REg00l]RF#;RG#;RH#;RI#;RJ,51RK5E1151IRI9E1E151FRF'6'6%;J,51151H,6I,6K'6151G/6Fg00m<'O'C'C%MA3L%NAP1P11D1?P8%K1CHP31D17CH%S1%T1RAPAPA!wl'1G1=RF1G12RG'B,4AEh%g5RK1?1:RI1?1<9f1F%^:,?1R:5]1!sK$C9PKPA1B:G,4APK!sw/P11?1;R;g00U4R:PIC@,4!sF/BE\F[!sZ$1PGg00U[P;!sJ%KP1PFP!sY'C9!s$%1_A6P0P8g00VBRAg00VbR6'F1`08=:A6dAa123Cbb>b?b@X21X31X41X51W1g00mh\>1I=?/<79:13[%=71278/7B112?12=?[[[[^21^31^41^51^1@P0f<R0!yx$<0='1P7P8P0P@PCPDf:f;O9b=b0bCbBb;b:b9b0b8g00oP/29eb7b6W<XA1o"). Qed.

(* Statement written out (rule 11g) because ONE PREMISE IS ADDED:
   [m_kernel mo' = m_kernel mo].  [KLB]'s new [kb_vdso_in] field reads
   [m_kernel], and this lemma's [Evm] constrains [m_vmmaps mo'] only, so the
   old statement no longer determines the field.  The text is the donor's,
   binder for binder, with that one line inserted after [m_halted mo' = None]:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/Spec/KLink.v -> KLB_mmap_new
   The only caller is [ev_mmap_core] below, where the model is
   [mmap_na_model]/[mmap_rw_model], both [with_vmmaps]-shaped, so the new
   argument is [reflexivity] under a [destruct isnone]. *)
Lemma KLB_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KLB L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  a mod 4096 = 0 -> 0 < a -> a + n <= alloc_top h ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  mminv mo' -> m_halted mo' = None -> m_kernel mo' = m_kernel mo ->
  m_channel_reader mo' = m_channel_reader mo ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KLB (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
(* Replay replaced by explicit text (rule 11); for the statement see the note
   above it.  Spliced by g3notes/bjhl/splice.py, which
   anchors on the declaration line and refuses unless it occurs exactly once
   and the two following lines are "Proof." and a KReplay replay ending in
   "Qed." -- so the blob was replaced without ever being displayed.
   PROVENANCE, cited BY BRANCH, read per hunk with git show:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/Spec/KLink.v -> KLB_mmap_new
   ONE DIFFERENCE from the donor, semantic rather than cosmetic: the donor's
   tree has already had [kb_resv] weakened to the prefix-existential
   [exists lo hi, vm_reserved = lo ++ hi /\ ld_resv L = rband .. :: map wwZ lo],
   so it opens it as (rlo & rhi & Hrlo & Hlr) and needs [Hrlo] to put an entry
   back into [vm_reserved].  This tree still has the plain equation
   [ld_resv L = rband (alloc_top h) :: map wwZ (vm_reserved h)], so the
   [pose proof] below takes it directly and the donor's [H'] step is not
   needed -- [H] already names membership in [vm_reserved].  Everything else is
   the donor's text.  The donor carries no address and no constant, so none was
   taken from it. *)
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n A1 A2 A3 Hrf Hmi' Hh' Ek Er Evm. pose proof alloc_ceiling_lt as Hcl.
  pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47]. fold h in Htop0, HtopC, Htop47.
  assert (Etop : alloc_top (m_vmmaps mo') = alloc_top h) by (rewrite Evm; apply alloc_top_same_sp).
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; symmetry; apply mmap_len_round_up).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kb_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ alloc_ceiling)) by lia. cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - destruct (kb_resv _ _ _ HK) as (rlo & rhi & Hrlo & Hlr). rewrite Hlr in H. destruct H as [E|H].
        { unfold rband in E. injection E as <- <-. left. exact A3. }
        apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        assert (H' : In (e, sz) (vm_reserved (m_vmmaps mo))) by (rewrite Hrlo; apply in_or_app; left; exact H).
        pose proof (region_free_InZ _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H'))) as D. rewrite Ua, Un in D. exact D.
      - injection E as -> ->. rewrite <- mmap_len_round_up. apply Dgm. left; exact H.
      - injection E as -> ->. rewrite <- mmap_len_round_up. apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (kb_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  kb_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            match ld_brk L' with
            | BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
            | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
            | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
                /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo')
                /\ (exists e, In e (vm_maps (m_vmmaps mo')) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
                /\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
                /\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
            | BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
            | BPDead => True
            end).
  { intros L' E1 E2. rewrite E1, E2, Etop, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  assert (Hlbb : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> lbrk_bytes L' = lbrk_bytes L /\ lbrk_cnt L' = lbrk_cnt L).
  { intros L' E1 E2. unfold lbrk_bytes, lbrk_cnt. rewrite E1, E2. split; reflexivity. }
  (* the two vDSO fields: the pair is in a ledger this grant does not touch,
     and the one new mapping is apart from every reserved entry because [Hrf]
     ran [region_free] over [vm_reserved ++ vm_maps] *)
  assert (Hvdi : incl (vdso_reserved (m_kernel mo') (vdso_top (m_vmmaps mo'))) (vm_reserved (m_vmmaps mo'))).
  { apply (kb_vdso_in_eq mo);
      [exact Ek| rewrite Evm; reflexivity| rewrite Evm; reflexivity| exact Etop| exact (kb_vdso_in _ _ _ HK)]. }
  assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps mo')) ->
                   forall e, In e (vm_maps (m_vmmaps mo')) -> edisj e r).
  { rewrite Evm. cbn [vm_reserved vm_maps].
    apply kb_vdso_disj_cons; [exact Hrf| exact (kb_vdso_disj _ _ _ HK)]. }
  assert (Hrdr : m_channel_reader mo' = true) by (rewrite Er; exact Krdr).
  destruct isnone; constructor;
    first [ exact Kresv
          | exact Krtop
          | exact Hrdr
          | exact Hvdi
          | exact Hvdd
          | apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | rewrite ?Etop, ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros e [<-|He]; [rewrite ehi_pair, Ua, Un; lia| apply Knwf; exact He].
  - intros b0 l0 Hin. specialize (Kgrp b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
    + specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kbreg b0 l0 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - unfold vm_live_bytes in *. rewrite live_bytes_cons, Un, Klive. unfold ltotal. cbn [ld_groups ld_metas set_metas]. rewrite sum_mlen_cons.
    destruct (Hlbb (set_metas ((a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [-> _]. fold n. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount. cbn [ld_groups ld_metas set_metas length].
    destruct (Hlbb (set_metas ((a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [_ ->]. lia.
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgrp b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kbreg b0 l0 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - unfold vm_live_bytes in *. rewrite live_bytes_cons, Un, Klive. unfold ltotal. cbn [ld_groups ld_metas set_groups]. rewrite sum_glen_cons.
    destruct (Hlbb (set_groups ((a, len) :: ld_groups L) L) eq_refl eq_refl) as [-> _]. fold n. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Kcnt. unfold lcount. cbn [ld_groups ld_metas set_groups length].
    destruct (Hlbb (set_groups ((a, len) :: ld_groups L) L) eq_refl eq_refl) as [_ ->]. lia.
Qed.

Lemma is_errno_form_neg : ltac2:(zQ "80!s4!ina!io2!re!hi5!hk3!rg7!rh6>1e$5>0@2$3@2$0+1^1@2$0^1+vvf@3$4$1@1$6@1$7^2$2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##4^h04__p1h16__sat1h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with91bh:2Heh;1ep;1p;2p;3p;6p;4p;7p;8g008Dj16Tg00@hj20Tg008bj18Tg00ADj2;Tg007_j12Tg009Gj2RTg00W_j27Tg01JNj2?Tg01KNj2>!sS$Ej2@!sS$dj25Tg01\7j2_!sw$_j2\Tg00BGj3V!s/$kj2UTg00CLj1T!s/$lj1STg00DLj2Q!s/$jj1OTg00EHj1NTg00F3j2:!s/$Vj2MTg014jj6LTg00Gdj1ITg00HFj1J!s/$dj3KTg00fhj3<!sJ$9j4ATg00Ikj2HTg00JMj2GTg00KSj3PTg00L2j4FTg04Wij4CTg005Fj6DTg03Vfj2ETg03WCj2^Tg06J3j1]Tg06HDj1[!sn$9j3W!sn$dj7XTg00MHj7Y!tC$Gj8ZTf0R0#8#8p=3g00VBR1g00VbR27W0p=1g00SjR3f1R4g00U4P0CAp=9P4g00MlR5g00NKR6P6g00NkR7P0g00OKFXp=4f2R8P5P6P6P7P4P0FYp==f3R9!s;+8P4P0GZp=Bg00<YR:#6R;/00R<%8:#3!s$+6R=,00R>';P1P2%2:R?#6R@%2?#2!s$%!s7$A'RRB/78RC/?BRD,>0#1X91P1P21>2!s3%1@12R217B4R1/?BRE%1E15CB[151!s4$D[1_1B1\@ARDg00S0RF/5@RG10FA15FB[RH[RI10F@RJg00SNRKAV@A4UW3RA10FB\K^3JRJ!vA$:@1UF@'@PGeO1RGPHp-0RKg00THRL#TRM%SLRL1Q34RN%O3RO%N3RP1:3;1M3:R:'9,4PPP!vO+9ELR95=P%I6R6P31:3@%J?5K3R?=<3:R@g00U[P?CA,4PCB1HP7R7P0P8P21G08#1dAP3F4CFRFb5b7b8X23W01;<4PE[^23^0KP0f5RE/0=PEf4R<O3b4b1b6b1CCED17B=RB/E1R8%1810BC[10B1R81EBC#1[1^B1PDPIPAPJPGPHPMPLPNPOPP1:3=R=,9:,4P9=P9P6A<3?=/9@!tx$P7P!t`,X0K1;4>P8!ta+10;EPEP!t\2%]4#[#1eW:X;3o"). Qed.
Lemma is_err_neg : ltac2:(zQ "80!s4!ina!io2!re!hi5!hk3!ms2!rh6>1e$5>0@2$3@2$0+1^1@2$0^1+vvf@3$4$1@1$6@1$7^2$2").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##2Hh02Hah14__p1h26__sat1h34__x1h41mh51nh61Hh72Heh87__arithh94__ffh:!sX%0h;8__varmaph<5__with=1ep;1p;2p;3p;6p;4p;7p;8g008Dj13Tg00@hj20Tg008bj19Tg00ADR0j2?Tg01JNj27Tg009dj22Tg01\7j2ETg007_j16!sA$Gj2ATg00W_j2:!sg$_j2XTg00BGj3V!s/$kj2U!s\$Ej2=Tg00CLj1R!s/$lj1QTg00DLj2M!s/$jj1LTg00EHj1KTg014jj6GTg00FVj2F!s/$3j28Tg00G9j4>Tg00MHj7H!s8$dj1DTg00HFj1I!s/$dj3JTg00fhj3<Tg00IGj8C!s/$kj2BTg00JMj2NTg00KSj3OTg00L2j4PTg06J3j1@Tg06=Wj1S!sJ$9j3T!sJ$dj7WTf0R1#9#9p=1g00VBR2g00VbR37T1p=4%61#6p=5f1R4g00MlR5g00NKR6P6g00NkR7P1g00OKFWp=;g00SjR8g00<YR9#3R:/01%99#1!s$+3R;,01R<'?P01741#4f2R0/24R=[12411704#4[R>f3R?/70#4\=1E41P1n20010!s#$12!s-%0X48X58P>^48^58P1%69R>#3R=%6>#5#5!s3$@'ARA%5!s7$#3RB':RC1:A01X=@g00S0RD/2=RE10D@12DA[RF[10D=RGg00SNRHAV=@4UW010DA\H^0GP4g00:@1UD='=PEeO1PFp-0RFg00THRE#R%QE1M84%L8%K8REP5P6P6P7P!s07?EGP81F89R9g00U4188;C>,;EFH%D6P8188=%I>5J8R>188B5<8g00U[A<8>9!sO$GC1BE7P1P01=231N10#4dAO8D4CPb9b;b<X38W11?4<1:A4,2C[^38^1FP1f6R1,0:P1f5O3b8b2b:b2O3b6%@4#S#4eW7W=o"). Qed.

Lemma live_bytes_In_le : ltac2:(zQ "91!htf!ig4!ij9!ila!isd!ivf!il4!s4!iia&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$3~0>1e~0>0@3$6~0^1^2@2$7@2$8@1$0#k0@3$4@1$1@1$0#k0@1$1@1$0#k0^2@1$5^3").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink ()) ["HC"] "##8kp'0h01eh14__x1h24__x2h33Hinh44mapsh52IHh67__arithh74__ffh84__p1h98__varmaph:5__with;4__x3h<1Hh=2H0h>2H1h?1ah@2a0hA1lhB1nhC1zi001bi011pp;1p;2p;3p;4p;6p;7p;5p;8g007_j16Tg00HFj1bTg018^j1STg01?RR0j2KTg00Clj1FTg01A8j34Tg01>4j33Tg01:aj21Tg01fMj12Tg00@hj20!s\$Lj1@Tg00c?j37!sS$Aj48Tg00XZj25Tg06K:j1_Tg01Yaj2WTg01ZTj1VTg009dj2ETg00ADj2DTg00K9j3=Tg00DLj2C!t$$_j1TTg00d=j4A!sA$jj1RTg00EHj1QTg00F3j2M!s/$Vj2<Tg00Gdj1LTg00fEj3?Tg00Ikj2JTg007Ej2NTg00JMj2I!tC$Sj3OTg00L2j4P!u{$Oj6HTg00]ej1BTg00^Dj2>Tg00jUj3GTg00agj2aTg014jj6`Tg00MHj7^Tg008bj1\Tg01gFj3XTg005Fj6YTg01E8j5Z!tp$9j4[!tC$dj7U!tp$Gj8]Tg00SjR1f1R2g00U4f0R3C[p=9P2g00MlR4g00NKR5P5g00NkR6P3g00OKFUp=:f3R7P4P5P5P6f2R8P2P3G]p=;g00<YR9#6R:#6!s$+bR;#SR</K<R=#FR>P=A4=32A3<<2,1;R?%28'0[^0=R@X4>%@=RA94=3g00mhA3<<8,1;RB%2A'0P3n010!s#%W3X0=P0P<P<A7=7894=3f4R0=7=7#2,0?[^0=\@^A>P3P<P<P0P7C8=7=!sP$P111;0%27R?'510B3XC1%_7g00S0RB/0?f5R?,W;11;?RA,0B%V;RC,EA'Dg01D^P<P<f7RAf6RDC8===7A4=7?A3<<0,1;11;A%2D'5'0P8!sR$8REPA!sP$0P=!s8$9RFPEC8RGA3<<3!s[%FRH%2ERI'5'0X0=g00THRJ#@RK%FJRLP11C18RMP2%T1CA%R1RN%Q1RO1M1B1<1:R:'9,:ORP%L5RQ1<19RRA?1!s=&C;1JO6RSP3P8g00VB!{I$VbRU'N1I38==TUdAO1B2CPRUb7b9b:X11X2110B2RB1528,02[^11^21P3PIPHP0O3b6A3<<G!u9%E%2ARE'5'0eP?P3EHW>P3O1A4=0DPDP?P3O!xk$?,1;/0Ep-0REg00l]RD#BRG#B,>11>1G1>1D5G15G1g00m<'a=7JKPLP1PMP21C17CAPNPOPO!zJ'PP!s2-?E`F^PQPO%\9,<1R9,9R,:OPQA?1:!s3&C;C;PSP!u_0X;1W81DB710271570,08[!ug&^;1^8EP3f:,1;RE/EC%2FPEA3<<A,1;P0P2O6b6b5W3P3O1n20!zk'211000!s'$b=b<!zM$?P0!zM$7#2AX?07EY!{8$X5@X4>XB<X?<P2P3O2!sn$10!s$$!so$100X@=P3DZW4o"). Qed.

Lemma mmap_addr_ok_intro : ltac2:(zQ "h10!htf!hk3!iia!hi5!ina!no9!ij9!io2!hk8!rle!rm7!hn3!hne!s4!m5!ho4!ig4>3len$1>1a@1$h0@1$0#k0>0@3$3$1@2$f@2$2@1$0#k0^1$8Z>0@2$eZ@2$2@1$0#k0^2>0@2$d@2$c@2$2@1$0#k0^3@1$b^4@1$9?2HC@3$3$4@4$a?2HC^5@1$5@2$6$1$1@2$2@1$0#k0^4$7").
Proof.
ltac2:(KReplay.run1 (kr_t_KLink ()) ["HC"] "h01bh12H1h22H2h32H3h41ah53lenp;1p;2p;3p;4p;6g007_j12Tg00HFj1KTg018^j1CTg01:aj23Tg00Z1j28Tg009dj29Tg013Cj16Tg00XZj27Tg02PCj1@Tg00@hj24Tg01JNj2<Tg01KNj21Tg03Vfj2?Tg01?Rj2JTg00CLj1ITg06LJj3GTg007Ej2FTg03WCj2DTg04Wij45Tg01\7j2BTg02;dj2=Tg06MOj2ETg06Moj4ATg00K9j3>Tg005Fj6HTg00SjR0f0R1g00S0R23>p=:g00VBR3g00VbR47>1p=0P3P4f3R5f2R6f1R7P1EHp=;g00<Y#2#2#2#2#2#2#KR8#C1381g00keR9'8#:1387,921386%65'7p,2HCR:#@R;'4f4R<,38R=,<2R>,11f5#6R?,7=R@/?;RA'11J00#IRB9G=?R?'1#0X031141/1A/1?#0X031144/11/1?#0X031F341385R8%6<'7R5/?;R4%0414@;[145;%0A[1D5;P1C5C;1<28R1%01192=[1928%0>[1B28P7C5C;1889R7/=2R>%0>18=9R=#:[%:71==2#0[1E72P6C5C;P:P<PBP8CA#0eW3W2W1W4X50o"). Qed.

(* [comment removed for export] *)
Lemma BUD_gap : ltac2:(zQ "h20!hk3!s4!re!htf!ig4!hi5!it4!kl4!klc!rn6!lh2!jk2!njd!kq7!ro8!hne!m5!ho4>1L$b>4pbrk$0>2mo$7>2nZ$0>2cb$0>2ck$0>0@3$d^6^5^4>0@4$c^7^5^3^2>0@2$2@2$h0Z^5@2$1^5^4>0@3$5$0@2$h1^6+hgg0Z>0@2$1+1^5@2$2@2$6@1$4@1$3#k0\1a@1$4@1$3#k0@3$e^a^1^9@2$1@2$f@1$9^9^8@1$a@1$8^9").
Proof.
  (* 08b1429: [mmap_grant_conds] carries the Linux placement ([Placement.linux_place_is]); the
     grid gap lies in [task_unmapped_base, alloc_top), so GapGrid.gap_exists_place gives a placed
     address with the four admissibility facts. *)
  intros L pbrk mo nZ cb ck HK (B0 & B1 & B2 & B3 & B4) HnZ Hal Hck. kb_open HK.
  pose proof (vm_backing_used_le_live' mo Kminv) as VB.
  pose proof (live_bytes_nonneg (vm_maps (m_vmmaps mo))) as LN.
  unfold vm_live_bytes in VB, Klive.
  split; [| lia].
  destruct (gap_exists_place (m_vmmaps mo) nZ (kb_thp (m_kernel mo))) as (a & C1 & C2 & C3 & C4 & C5).
  - unfold GRID_W, BUDCAP in *. lia.
  - exact Hal.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin].
    + pose proof (Krwf e Hin) as Hr. unfold GRID_W. lia.
    + destruct Kwf as [Hb _]. specialize (Hb e Hin). pose proof (live_bytes_In_le _ _ Hin) as Hle.
      unfold elo, ehi, GRID_W, BUDCAP in *. lia.
  - rewrite length_app, Nat2Z.inj_add, Kcnt. unfold RESV_MAX in B4. lia.
  - exact (proj1 Ktop).
  - exists a. unfold mmap_grant_conds, MmNodes.wz. cbv zeta. repeat split; assumption.
Qed.

Lemma ev_mmap_core : ltac2:(zQ "i30!hk3!mk5!rpd!ina!re!no9!jka!ij9!kl4!qgf!rq8!s4!m5!hi5!rr0!rrb!hn3!rsb!qt1!ola!jk2!njd!kq7!pg9!ph9!pm3!rt4!rtb!ru6!pn2!oq4!pnc!po4!rh6!ohf>1L$h4>1G>0$1>0$8P>2s0$1>3len$0>6isnone$3>2cb$0>2ck$0>0@1$h8^6>0@1$h3^8>0@2$4@2$cZ^6@2$c^6$h2>0@2$b@1$h0^7^5>0@2$b+1^5=4prot$0M3\6isnone$3$0^8$hb$hc=3dec>3rsp$9@1$6$2M3\6isnone$3>3rsp$9@1$6$2^9@3$f?2HC^a@1$5@2$7$0$0@3$e?2HC^a@1$5@2$7$0$0@6$h9$hd$1$0\1s$1\2mo$8@2$4@3$d$1^2^e@2$4@3$h6^h0@1$i2^2^1@2$4@2^f^2^1@4$h5^h0^1^b^a@5$he$1$2$0@4$i0$1$2@4$h1Z^b^2$a^1\1a$2@3$hf$1$0M2\1a$2$0^1\1e$0@1$i1^1\1x$0^1@6$h7^e@4$haZ^b^2$a^d^c^9^8").
Proof.
  intros L G s0 len isnone cb ck HG Hq Hlen Hcb Hck prot dec.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_aligned len) as Hna.
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ G s mo /\
                match x with
                | MmErr e => False
                | MmOk a => KLB (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false
                            /\ BUD (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) mo (cb - mmap_len len) (ck - 1)
                end)).
    intros s mo (-> & HK & HGs & HB). pose proof HB as (B0 & B1 & B2 & B3 & B4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47]. pose proof (kb_hceil _ _ _ HK) as Khc.
    pose proof (kb_live _ _ _ HK) as Klive. pose proof (live_bytes_nonneg (vm_maps (m_vmmaps mo))) as LN. unfold vm_live_bytes in Klive.
    assert (Hl62 : 0 < len < 2^62) by (unfold BUDCAP in *; lia).
    split. { cbn. left. subst prot. destruct isnone; splits; auto; lia. }
    destruct (BUD_gap L (ps_brk s0) mo (mmap_len len) cb ck HK HB ltac:(lia) Hna Hck) as [GAP BK].
    intros rsp mo' evs Hst.
    assert (Hcase : exists a, mmap_grant_conds mo a (mmap_len len) /\ dec rsp = Some (MmOk (bv_unsigned a)) /\
              mo' = (if isnone then mmap_na_model mo a (mmap_len len) else mmap_rw_model mo a (mmap_len len))).
    { subst prot dec. destruct isnone.
      - apply (fun X0__ Q1__ => proj1 (nstep_mmap_na_iff mo _ _ _ _ Q1__) X0__) in Hst; [|clear - Hl62; lia]. destruct Hst as (_ & [(_ & _ & NOGAP)|(a & C & -> & ->)]).
        + exfalso. apply NOGAP. exact GAP.
        + exists a. split; [exact C|]. split; [|reflexivity]. destruct C as (C1 & C2 & C3 & C4).
          unfold dec_mmap_none. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite !bv_eqb_refl. cbn [andb].
          rewrite mmap_addr_ok_intro; auto. cbv zeta in C3. change (pgup len) with (mmap_len len) in C3. lia.
      - apply (fun X0__ Q1__ => proj1 (nstep_mmap_rw_iff mo _ _ _ _ Q1__) X0__) in Hst; [|clear - Hl62; lia]. destruct Hst as (_ & [(_ & _ & NOGAP)|(a & C & _ & -> & ->)]).
        + exfalso. apply NOGAP. destruct GAP as (a & Ha). exists a. split; [exact Ha| exact BK].
        + exists a. split; [exact C|]. split; [|reflexivity]. destruct C as (C1 & C2 & C3 & C4).
          unfold dec_mmap. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite !bv_eqb_refl. cbn [andb].
          rewrite mmap_addr_ok_intro; auto. cbv zeta in C3. change (pgup len) with (mmap_len len) in C3. lia. }
    destruct Hcase as (a & (C1 & C2 & C3 & C4) & Hd & Emo'). exists (MmOk (bv_unsigned a)). split; [exact Hd|].
    assert (VO : vm_only mo mo') by (rewrite Emo'; destruct isnone; apply vm_only_with_vmmaps).
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact VO| exact HGs]|].
    assert (MI' : mminv mo') by (rewrite Emo'; destruct isnone; apply mminv_with_vmmaps; exact MI).
    assert (HH' : m_halted mo' = None) by (rewrite Emo'; destruct isnone; rewrite m_halted_with_vmmaps; exact (kb_halt _ _ _ HK)).
    assert (Evm : m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                 (if isnone then (Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                 (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))).
    { rewrite Emo', Z_to_bv_bv_unsigned. destruct isnone; reflexivity. }
    destruct (KLB_mmap_new L (ps_brk s0) mo mo' (bv_unsigned a) len isnone HK Hq Hlen
                ltac:(rewrite page_size_eq in C1; exact C1) C2 C3
                ltac:(rewrite Z_to_bv_bv_unsigned; exact (proj1 C4)) MI' HH'
                ltac:(rewrite Emo'; destruct isnone; reflexivity)
                ltac:(rewrite Emo'; destruct isnone; reflexivity) Evm) as (HK' & Hans & Herr).
    splits; auto.
    unfold BUD. assert (Elim : vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo)) by (rewrite Evm; reflexivity). rewrite Elim.
    unfold ltotal, lcount in *.
    assert (Hlbb : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L -> lbrk_bytes L' = lbrk_bytes L /\ lbrk_cnt L' = lbrk_cnt L).
    { intros L' E1 E2. unfold lbrk_bytes, lbrk_cnt. rewrite E1, E2. split; reflexivity. }
    destruct isnone; cbn [ld_groups ld_metas set_metas set_groups length];
      [destruct (Hlbb (set_metas ((bv_unsigned a, len, 0) :: ld_metas L) L) eq_refl eq_refl) as [-> ->]; rewrite sum_mlen_cons
      |destruct (Hlbb (set_groups ((bv_unsigned a, len) :: ld_groups L) L) eq_refl eq_refl) as [-> ->]; rewrite sum_glen_cons];
      rewrite Nat2Z.inj_succ; splits; lia. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & Hx). unfold ev_step_post, ans_cont, ev_costb, ev_costk, ev_fixed.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED_Z =? 0) with true. change (Z.land MAPF MAP_FIXED =? 0) with true. cbn [negb]. cbv iota.
  destruct x as [e|a]; [destruct Hx|].
  destruct Hx as (HK & Hans & Herr & HB). rewrite Herr. subst prot. destruct isnone.
  + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
  + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok : ltac2:(zQ "h80!hk3!mk5!re!hi5!kl4!rq8!rt4!s4!m5!im2!hn3!qt1!ola!jk2!njd!kq7!pg9!ph9!pm3!rtb!ru6!pn2!ruf!ohf>1L$d>1G>0$1>0$4P>2s0$1>3len$0>4prot$0>2cb$0>2ck$0>0@1$h1^6>0@1$c^8>0@2$9@3$3$0^5$h3@3$3$0^5$h4>0@2$2@2$8Z^7@2$8^7$b>0@2$7@1$a^8^6>0@2$7+1^6@6$h2$h5$1$0\1s$1\2mo$4@2$2@3$3$1^2^d@2$2@3$f^f@1$h7^2^1@2$2@2^e^2^1@4$e^f^1^a^9@2$h6?2HC@4$6Z^a^9$5@6$h0^d@4$6Z^a^9$5^c^b^8^7").
Proof.
  intros L G s0 len prot cb ck HG Hq Hprot Hlen Hcb Hck. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L G s0 len true cb ck HG Hq Hlen Hcb Hck).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L G s0 len false cb ck HG Hq Hlen Hcb Hck).
Qed.
End HC.
(* [comment removed for export] *)
