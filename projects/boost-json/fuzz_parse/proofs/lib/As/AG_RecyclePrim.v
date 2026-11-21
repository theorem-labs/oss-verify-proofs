(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit AW_Efs SecLazy AS_Refill1 AS_Refill2 AS_Rta AS_LcDealloc AS_RecyclePrim AG_WFHit AG_Malloc AG_Malloc2
     AG_MallocModel AG_ColdModel AG_Refill2 AG_Refill3 AG_MallocCold AG_RepQ AG_RepQFacts AG_RepQFacts2 AS_Free2 AG_RecycleModel
     AG_CacheDealloc0 AG_CacheDealloc1 AG_CacheDealloc2 AG_CacheDealloc3 AG_WriteSet AG_RecycleDefs AllocTacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import PerfLia.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_RecyclePrim () := KReplay.lz_vm "#&knI56Stdlib5FSets<FMapPositive;!s/'Map4tree00C47Corelib4Init5Logic8eq_ind_rC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd;ex_introF17C13~~~!slP2As8AllocRep4a_st!sj&7!sjN>Asan!sk$Model9as_chunks!t^[G_WFHit7keys_ok!smY7AG_RepQ5ARmem!v9b8inst_rep!snb9flags!sof:thread!spf7sec!smf6ia!sl-!{|'6ZArith6BinInt1Z2le!sB>tI!|,73and00!vH]region!w:gpclas!x+gA!tb&shadow!swf?!sw&junk!zeg!}v$!so-!~m^5as_tq!snigq!uOY?!~j$cycle!#4Q$del_state!vGb5a_thr!skectx!skefsb!skb3a_L!sieS!sib4a_Zr!sjeAL!xKfop!skebo!#<D%K!vs]st01!|Re;ch_user_beg!st%!#6p72eq!#@993not!}3c6!}3#in!uD&!t475proj1K!#8[;1!tQP!#A_%:and_elimF9!vge:!#5w$li!#Ag'4!#D6&Lists4!s+#2In!t2_7qc!t//!yR[;batche!#:U,I!#7+^!uo$00!sp&!{7`0!uP[sS!#;~#3!#C^'!{+,7Numbers7BinNums1Z00K!sD?1!|^`kNumClasse!#Fk%!zs29Datatypes4!x9#02!ucS!#FD&<AREPQ_placed!vVY!sq'9!sq%WFQ!snh!#H'd9!uL%!#I`c3!uId8WFQ_key!x;4!yO62!yO_8ch_!#D{#!t7C8p!#PR%!t>a:!#F8$size!#5Sd<!u3#!#5V#!#9='!su_=!tj%of_addr!sve:in_primary!ssf!#H#%!u`h!vW#a!s4#!su-!#L|:3add!u/`get_!u3%!u/eArg!u/%ated!#?$#!sze>rg_mapp!sw1!v,<sub!sC<6moduloC!#:v`_rz!tSCdiv!sC=mul!}~G3I!#8q;bool!#:M-!sF8!#:O_@kC!}o#HeaderS!~l,!#7aWKit6carv!#:/'!#CR;!#;=S@AG_CacheDe!z6$1>!t7%_not_31Q!#65L!#Du82eq!s@4!#=B21I!sFA0K!#Cz&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr02!sIE1K!t?L!sQ75Tauto8G!sJ'7!vZ<6option02C!sl<B!sl&!sH6:Z!t^+=Z!sT$CheckerC!vl<4find!sqAC!sq0_sound!u[F4!sJF5!sJF8!v%<5eKind!y~=uni!y~9!se%4kind!{-?!sf$1I!v;@;!#4v$!}K$!t:8!y=13Op2!ydF!sM$3!sMI5!#Q;75False!|tB1!sD@3!#Qab<WFQ_del!#?6#!#3z$c!syR>!sy,Prim9armem!sz#!#62=6eq_sym!#XK^!#[Q\!#Ms%5aceil!#8m^!tW%pa!tWb4aap!#Y{dkobj!uCcdisj!#A-d6as_sec!soe:sc_map!#Eqh;!ss&!#J@,!#@w;pow!vc\2RB!wMb2FA!uee8round_u!#o\cch_end!slb9!z]$_env!sob8!|:#!sn]!#BT207cd_pur!#PBfrg_num_fre!#D]'!su^D!#J[+!sx#_arra!#OTe=rg!sv5!#@x;length!#K\<to_nat!#32_get_p!#32e8pc_coun!#}uf!sq#!#}u-!sr^4zle!#QUe9max!uU0!{^cA!#X}%lots!t#_!#\F&:WFQ!#T;0!soT!tf#Wf;ro!|U#!|T/!spR=!ta&Facts2;record_extQ!sv[!#4&%!sw$5ch_lo!x@e7!#ng$!uZh<!#]B$alignQ!tie;compute_re!#zte9rq_need!#5kf:ch!#^71!#E3:in!#\J_<as_space!#?b,!#:QWKit=!#_G+_!vog?!#7f+_bas!#X/bB!su2!tr,!#8E:7div_mod!sG<=mod_pos_boun!sMBneg!sM25!#LR#8PreO!s/#1Z;!t>#0_r!}z#!sL>!st#!sL&!#iM?3!#VJ=3Pol!#P}=3nat!#W27!#OZ05Psatz!#W[?!t7$!tXD!#XEE4!wm=ad!v/$!#TJ59SatDivModCZ_!v|#non!wO#!s,%!xgAposK!#SuL3!#KS\a_ri!{B_Rep7a_cach!#IfB>pow!zn$!uvB:!sN#!sJ&!vsB!{A$!vs/!zQ>N!xVG7!u{P!#~P35!vhV!$Av&!sk+14!#=r`F!#qZ+_table_facts!ti]!uV,6!sk%!#]BE3!{E=compare!~>K4!sOK6!sOK7!sOK5!}9N!ysF5!sIE!#lC<:!vU%ison!#]b7!tf;1!~5U!#Y#%6AHI_LO!#?6ekSpaceS!#y'g9kPag!srj@kPtrArrayReserv!$<tb8AFS_SIZE!sn%!$/F^6s!$/G/!u\_>kFree!u]$!vUiA!sw,Map!szi<kUser!sul@!tq,Offse!#N6%I!#?Y?!$IRS5ASegs8AIMG_TOP!#5s&!t2?1!#hr74True00!#g:a8rp_gpo!$7P&K4ELinuxProcessSemantics?!s<23Run6config01C45stdpp9bitvector;definitionsDbv_unsigned_in_range!sYA;!sY-!sPA:b!#Fn#ulus!wOS9!}8'X8awin_vi!$UJY!so,:!$S$#x!$L3\!sq,7AMODELX!#3da6!sm%!t\dakerne!#kYb?amaps!xs#ledger!sud!$Q:%visibl!#70b7ABUDGET!#3Pd7as_!u`#!spfmp_ki!#fc&K!sp^5m!#wW#3!spl4!#5u&!}V?2bv00!#yZ<prod00!v?c!#Sq,!t[@7Z_to_bv!t>c!#nf+K!uPA1C!#6MI5State8m_vm!yN$!s]P7vm!z+$!$L}8or!wG4!$,]&x00!t8Q;vm_noac!s;#!vcP<LazyRestrict:!#8S&!#xv'!sqO:!sq#L!#3E#9nooverlap!sna>entries_nowr!ssX!uV1eager!#ay-!sq\;pages_tota!#{UdPh!#Tc&!zTQvm_limi!$SBS!#iP5d_cell!$Af$rep!#]e%K!#PnR5C!sl#4!sr#!$VX'!sjS4TacX2wz!tQf2!#5`%!v>R:AS_Refill14RENV!#I-f8ch!$aR-!uM`3!z0cjunk!wdZ3Mem5wr_a!$V@[!#QG%2sh!shb3n!sid8poison!~n+3!#:D$7tac!}-#<f_equal_help!#33\8r!s/&!w:Z5Frame3mkR!sgZ8PropExec7seg_rom!zCV2As<!yW$WalkKit6hidden!~E\9LiaTuning9zify_don!#=R'!#ZoH3!tBT6M!#67#C!#?U%_!#L<-!u<%!#}M;eq_dec!#=F16Specif7sum!$H47!#>$+1!#q+79!$:+#_ind!s_<2!#J:\:ak_resf_!#9UX<map_contain!#O&]7ak!$;/,!sn]8ak_zr!$9y[!t_1zr!#3AZ!sn,6ak_l!sm[;!sm$Budget6pusage!uNga!$mq+!$6g;eqb!t3S>!#;W#!#WA'Ar!s2%!xF$_!#WJ+!#Jm;!$I5&0!#_'O6LazySR4lzok!$fUW!~Q-6r!$/Z-!uuR6!uu#ta7rta_mf!$?aY!#?;+29rf!#Sn_!wU24rp_W!spY<AS_Lc!#D5%5lcd!soX!#:B+5munch!siawmono!siZ3Mem7mem_i!$:L'!#7x;shiftr!|6=ltb!#6/P=!#Y:#subtract!$80;3app!wnS7Sec!{t#:nonvm_sam!#S^'!#P5Rr!#j;$d!#8[Qvm_m!$DF#ase!saQ6vm_brk!#xp<ltb_irrefl!sJ<8sub_diag!#=7>b_eq!#tW<!sF#neq!~ZUW_Efs7efs_new!|uY!#N/3?cd!#J+$_fields!s}j8!s}'!sv&!#Kv]?addr_to_!#tX#!#F9&!#]4^6!%4W$!%#Xf<as_ptr!$B//!$-c'!%A%@1!$Aq_=as_n!|Q,!w+fs!$&L$_init!sxg@as_internal!s{$!sye7as_qmax!spki!$B{f!sp#!$,~,!zW`!$8{$!#L8W!}<7!$Z~#!}@2!szb3:kr_of_flag!sxj=froom!s{2!#6~;leb_spec!#;u=eb!#D-;8BoolSpec!#gyQ8HeapCeil5h!$[~^!#UC%;!$\k#!$/f[!#H;/@sh_!st#ing!#v6%!swX>!sw'!$G_%!#Au#_agre!swW!#A{+7outsid!$%9c!tX$_!$J~W!$4x43!zxi18ZC!$M[#W!uTb!$Xo%li!#]aY!$J/0A!$sR%vs_!%Lt$Q!x0`?stk!}S#rw!#ep$!ss[!#am#:!#f[$!$_mE6of!$V]#!vr[@!u,#transport_pt!t>B;lt_ge_cases!uST3Mem2w!#NN&!#EkI>Riscv!sE+5wview!tIX3mr!#xM&!#RWB!#[E88iff_!#Fv#!#^04;Zify!%7k%3inj!sIB9!|u#morph!sOB7rew_iff!sMB;!sM&_rev!{$Z9!xy#mer!#5r'!uy13Nat!%,e#!y124Znat5Nat2Z7inj!tz%!v[67!tl#sym!u?B5mkre!#Jw=max!#:w7!tU%Z2!tW#id!{v\E!#h/&!{{7!s{R:!#3v#!#V@#<!s}+!$o,[!%%C4!#rW#_after_c!%=ea5!%<u#!thj=!$1}#!tga!s{4?!$21%!s}2!#]7U;lzok!#|#%!slV9!sl#NodesFlazy!so&_okb!#{=0!wPS!#V1%?!#V1+!#aU-!v]b2@amodelx!w]s>depot_avoid!s|\=AW_D!sn#!#47#;!sy-!sv[!#>$-@!#>$+!t$$Q!~,[s!tr$Inv4d_nb!slg!%Ybc!$rJ$!#AI'!#:w+!%PP$7!s+#Def6Foral!$ZU/!sG92I!sGB0!#9TS!$Q:/!$R|&!#8S&!%RG,;!t0%_impl!yWa?DEPOT!#7h+!wpd5!sw$!smY>AG_M!|:$!#V@$!~7$but!%f5%!s{Y<!}=#old!sy$;in_mem_hig!#fI&!#<,:4ones!sD=la!$bi=9!sD#_!sg$!t|R!%/w2Dcb_!#nQ/ev!$0dZ!t%3>rec!sz%!$'C-!$6t:1!$I&e!#6U#!u3Y;AG_WriteSet4avm!%f<Y!#RD+9!#68$cov!{Y[!zj'2<!sq%!%V%^!uU/6aco!~6#!|Q\!w<&Defs4a!$J@[!sp25pendz!sqh:alive_ke!#D\Z!ti3!sv$!w?e9!yn#!#n?/!#6x4:in_app!#I1#!t9^5awr!#TJZ!sn/?!yB%_of_!#tMZ!vn5=!yK#!sy#!#t]Z!#GS,6WFQ_xb!ska5xb!%]B]l!$gS#!#@h&!#lj#!%fd\!%$//!%NJ/!soR!$~E0;NoDup!yp$!#|#%I!z;65!sL$!%m@97!$77%!tWS!#E}39ZC!uP`<!#E$-!w='in!${G$!#E#&!#ZC;divid!&$B<:mod_!sJB<!sF%!#@c$!sL<?!sL&factor_r!suDad!&2PR!v|7<!v|+_s!$#4Z!#DU/3!skg2!sk]9ex!#d3%!#64&!#~[:s!$}+-!#ty@8elementsC!#H293map!}r[7!}r#in!%EuY!x@46ZC_rec!stj9!st%!y3`!#hg,7!slh0!slg21!zh^!y{+9!w-Y!$2v1C!#Gz/sreac!}Ch7!skg8!w4g4!$OG&!#[<OSR!v$#6!v/%!$9O[4Step8!#lM1!#:n53!#eXR!#T}-5w!#=\Y!#iZ#Arr6u32arr!shZ!$K?%st!$P<Z!$Tz$b!x[&!$RS_!#V$%!%$<E6!tuT!$>c%2M!&3'&!#7795skipn!sD;6firstn!$$Y^7mapping!$$Z&!$LyJ1!#jdDapp!sKB6!sK$2!#~a<max!#;?<fs!$0h_>!#F2#i!$nB#!%~;+!sw^:!#VS+!#6LX!#Qe0stat!#Z;Y!$yO$5aseg!#h-V4Scfg=hunspell_scfg!y3'!wR:!%r1$2I!|}_!$^1eIk!s6#HeapLeftRedzoneMagic!#7\U!$1j2c!#Zn#!tu'K!sqf!#9B&!#y~X=machine_!tf'!#6jYivl!v<f!$<Y%0!sqf!$5s%!x~f7PROT_R!$'}&!#4;48ZifyInst@!$$T$_!%X:$!$C]-5!#4A#8PeanoNa!#y{Kadd!u{`a!z+t1!z+Q!$Gq$5!si$!$SMQ!#9Y:!y3f!$yg%!v5f!sp&2!spl6!spl!#F$&!wpP9page!$1#$!#D&Z;PCLAS!%99-!sq\?REGIONINFO!sug3ATP!sib4ATSD!#3YdB!#9Y'Fre!#9R-!#lQ7!%6W$!&B:aR!#5f#!&-d\!$a0/B_PRIM!u~e@kC!$Ne$PtrSca!#A%&!#5J_!$H,$!#8G'!#7U=7Inj_Z_Z!vwaHighMemB!%t#g!st'E!%0p&!v%`effect!v%4!#OL,8nil_co!#_q,!#[CA3key".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~04a_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~k45ARmem69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~o95chunk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAG_RecycleModel~~~~~~t29del_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AG_WFHit~~~~~~hi37keys_ok04a_AL03a_L03a_S04a_Zr05a_bot05a_ctx05a_fsb05a_thr05a_top03ast05mkAst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hr13memo99as_chunkso9achunk_list36Stdlib5Lists4Listigf2Ino96astate37Corelib4Init9Datatypesij14listo96effectij14prod37Corelib4Init5Logicim22ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~incfsame_but_shadowij14Someij16optionij14pairim23andim22eqo9acb_recycle3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsjg7dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statejkf5Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecycleDefs~~~~~~jo6arstep_post99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecyclePrim3HCW6RPStep~~~~~~jt88rp_model3h5LinuxProcessSemanticsfLinuxProcessSem3Runkj35mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~km85asegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~kqc6sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~kufdhunspell_scfgjt88rp_gpost37Corelib7Numbers7BinNumslk31Zo9cch_chunk_begij14consk45AREPQij14boolij14trueo9ach_primaryo9bCQuarantineo98ch_stateo96cstateo9fas_cache_inited79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~lt18awin_vislt1aflagsx_replt17AMODELX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~mj55DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~mnecdepot_placedlt19depot_cov79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mtb7mem_invhr15aceil46Stdlib6ZArith6BinInt1Zni92lelk34Nposni93add35stdpp9bitvectorbdefinitionsnl6bbv_unsignedni93powni96modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~np33stk03ATP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~ntb6B_PRIMntb6pusage69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~oj04lzok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~on12wzij14None69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~ora8restrictnp33mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~pgc2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~pkf7seg_romnl67Z_to_bvnl62bv" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma armem_del : ltac2:(zQ "h40!je!o1!sa!hh7!hm1!hmc!hn2!hn7!hnc!ho2!ho9!hp0!hp7!hpe!hq5!hqa!huf!hv6!ig2!ii2>1s$e>2ch$2>1m$h0>0@1$4@1$h1@1$0^3>0@3$h3$2^3@1$h2@1$0^4>0@2$1^5^3@2$1@a$f@2$3@1$0^6^5@1$c^6@1$a^6@1$b^6@1$6^6@1$7^6@1$8^6@1$5^6@1$d^6@1$9^6^4").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_RecyclePrim ()) ["HCW"] "##5Uh02chh11ch22BGh32BTh42CHh51Fh62Hxh71Ih82IAh92INh:4KEYSh;2RCh<2SCh=1Th>1mh?5nd_i1h@1shA1xp;1p;2p;3p;:p;5p;4p;<p10000p4p710R0!s4$_!s4%p8P!s6$1=!s6'g002Cj11Tg003Gj1[Tg004Sj1VTg005Zj2OTg006^j2NTg007fj2FTg008oj2ETg00:9j2DTg00;@j2CTg00<Fj2T!s/$bj2STg00=>j20!s/$Yj3KTg00>cj3JTg00?mj3ITg00A>j3HTg00BMj2GTg00CVj1?Tg00D^j1;Tg00Efj25Tg00G6j1:Tg00H;j1@Tg00I@j19Tg00JEj1=Tg00KHj1>Tg00LKj1ATg00MOj1BTg00NSj17Tg00OXj18Tg00P]l:6Tg00Qbj1<Tg00S0j3M!s/$Jj1L!s/$cj5RTg00U0j4Qj3P!s2$Kj42!s/$fl<UTg00Vkj1ZTg00X8j3Y!s/$Oj1XTg00YYj2WTg00ZdR0f1R1f0R2#Z3Yp=4%X2,W1p=3g00[ng00]3f2R3#1#[#Vf3R4#1,43f4R5/O3f5R6/N4R71F641E641D641C64g00^6R8g00^T/T2g00_2,S2'0R9f7R:?K61AJ:61AI:61AH:61'0'0'0[]1f6R;#1,421G61[^00%16R<#?,34%;<,3415<5%:6%@6%96%=6%>6%A6%B6%76%86M:6/O41F;51E:6f8R</D;f9/C:f<R=f:R>;K1AJ=>1AI=>1AH=>!tK&\9^18%1=R?,42f;R@/G!tO%??,3>f=R>#1#;,3@f>R@#1R?/5>%:@%@@%9@%=@%>@%A@%B@%7@%8@M:6RA/N=1FA=RB1EA=RC1DA=RD1CA=REf@RF#1RGf?RH'5RI%:F%@F%9F%=F%>F%AF%BF%7F%8FM:6RJ?K@1AJJ@1AIJ@1AHJ@!u-/R9%1H/5@%:H%@H%9H%=H%>H%AH%BH%7H%8HM:6!vw$RJ1G@!uP$R@%1ARA#?,3=%;A,3='0RA'0RK'0RL'0RM'0RN'0RO'0P<PBPOP:PCPNP;PDPMP6PEPLP5P9PKP4P@PAP5P1141GR5%<1%<H5M8#LRA141IfA#1RI,43%<3%<F!s@$'0[105A15IF,43[PGPHP>P=P1DRP2CQ3PO2X6JXA!wH%=%;?,3=P1P2C!s$2W2W3W4W;W8W<W=W5X77P2M<UW?W9W:W>X00W@o"). Qed.

Section RPStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (ch : chunk) (d : depot) (lo cb : Z).

  Let st : ltac2:(zQ "10!ii8$0") := ltac2:(zQ "10!je@1$0?1s").
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let CA := a_cache s.
  Let c := ch_class ch.
  Let U := ch_user_beg ch.
  Let mch : ltac2:(zQ "10!llc$0") := ltac2:(zQ "10!lm1@1$0?2ch").
  Let p := ch_alloc_beg ch.
  Let rz := ch_rz ch.
  Let nu := ch_used ch.
  Let csz := class_size c.
  Let idx := (p - RB s c) / csz.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let pc := get_pc st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let cnt := pc_count pc. Let chunks := pc_chunks pc. Let mc := max_count c. Let n := mc / 2.
  Let drained : bool := cnt =? mc.
  Let k := if drained then n else 0.
  Let mfa' := if drained then rta_mfa nf n mfa else mfa.
  Let stD := del_state st ch.
  Let sD := mkAst stD TH CTX (a_fsb s) (a_L s) (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).
  Let st' := cd_state stD c p drained.

  Hypothesis RQ : ltac2:(zQ "30!ln0!llc!ln8@5$2?5HCEIL?1s@3$0$1?3mch?2XC?2XB?1m").
  Hypothesis CHIN : ltac2:(zQ "30!sa!ig2!ii2@3$2$0?2ch@1$1?2st").
  Hypothesis PRIM : ltac2:(zQ "40!lo0!lo8!iv4!lp0@3$2$0@1$3?2ch$1").
  Hypothesis QUAR : ltac2:(zQ "40!iv4!lpd!lqb!lr6@3$0$3@1$2?2ch$1").
  Hypothesis INIT : ltac2:(zQ "40!lo0!lo8!iv4!lrf@3$2$0@1$3?2st$1").
  Hypothesis AX : ltac2:(zQ "30!iud!mh0!mhc@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!mia@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!kq3!mn5@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!mre@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!mse@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!kq3!nh5@2$1$0?1m").
  Hypothesis LO : ltac2:(zQ "20!ni0!nk1@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!nk7!nkf!nk1!nn3@2$2@2$1?2lo+ir0@2$3@1$0#k0?2sp").
  Hypothesis SPT : ltac2:(zQ "50!nk7!nkf!nk1!no2!nn3@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SPA : ltac2:(zQ "50!iv4!nk7!llc!no9!nn3@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis ST : ltac2:(zQ "40!nk7!kq3!nsf!nn3@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis TP : ltac2:(zQ "50!iv4!nk7!llc!nt6!nn3@3$0$2@2$4@1$1#k0?2tp$3").
  Hypothesis PROOM : ltac2:(zQ "40!ohc!oi6!nkf!nk1@2$3@2$2@1$1?2st+kqgg0$0").
  (* [comment removed for export] *)
  Hypothesis CBR : ltac2:(zQ "60!nk1!iud!nk7!nkf!no2!nn3@2$1@2$0@2$5@1$2#k0?2sp?2cb@2$0@2$3?2cb+8@2$4+2+jf").
  Hypothesis CBC : rw_cells asegs m cb [C8 (wz CA)].
  Hypothesis OK : ltac2:(zQ "60!klf!kq3!hn2!hn7!hnc!om9@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : ltac2:(zQ "e0!nk7!oqc!or2!iv4!jje!kq3!hn2!hn7!ov9!pg5!pk9!poe!pp9!pq4@3$3$4@3$8@1$6?1s@1$7?1s?3msF@7$a@hf$9?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$1?2cb@1$1?3mch?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$c@1$0#k0+mrjpc?2fc@1$2@1$d@1$0#k0?1m@1$b$5").

  (* [comment removed for export] *)
  Definition rp_model : ltac2:(zQ "10!ii8>3stX$0P") := ltac2:(zQ "c0!ii8!ik9!il1!ila!in6!is0!it3!itb!iu5!iud!iv4!iva\3stX$0>3stA$0>0@2$5^1?2st@2$4$0\4stA'$0@2$4@1$1$2\2ev@1$1$2@2$9@3$a@1$7@2$3$0@1$1$2@2$b^4?3mch@2$6@2$3$0@1$1$2@4$8$0@1$1$2^2^1@2$5^2^5").
  Definition rp_gpost : ltac2:(zQ "20!jje!jnd>0$0>0$1P") := ltac2:(zQ "20!jsa!ki7@hc$0?5HCEIL?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1s?1d?2lo?1m?2mo?2XC?2XB?2XB$1").

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st (mch :: XC) XB. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let MEM : ARmem s m. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok s /\ WFQ (a_st s) (mch :: XC) XB. Proof. exact (conj PL WQ). Qed.
  Let KEYS : keys_ok (as_chunks st). Proof. exact (WFQ_keys st _ _ WQ). Qed.
  Let GEOM := prim_chunk_geom st XC XB ch WQ CHIN PRIM.
  Let DCL := del_class st XC XB ch WQ CHIN PRIM.
  Let HC' : 1 <= c < kNumClasses. Proof. exact (proj1 GEOM). Qed.
  Let HC : 1 <= c <= 30.
  Proof. pose proof (carved_not_31Q st _ _ c p WQ (proj2 (proj2 (proj2 DCL)))) as N31. clear - HC' N31. unfold kNumClasses in HC'. tlia. Qed.
  Let HCC : 0 <= c < kNumClasses. Proof. clear - HC'. tlia. Qed.
  Let WQD : WFQ stD XC (p :: XB). Proof. exact (WFQ_del_prim st XC XB ch WQ CHIN PRIM). Qed.
  Let RQD : AREPQ sD XC (p :: XB) m. Proof. split; [exact PL|]. split; [exact WQD|]. exact (armem_del s ch m KEYS CHIN MEM). Qed.
  Let OKQD : placed_ok sD /\ WFQ (a_st sD) XC (p :: XB). Proof. exact (conj PL WQD). Qed.
  Let CLS : class_of_addr stD p = c. Proof. symmetry. exact (proj1 (proj2 (proj2 DCL))). Qed.
  Let CV : carved st c p. Proof. exact (proj2 (proj2 (proj2 DCL))). Qed.
  Let AMXD : AMODELX sD mo. Proof. exact AMX. Qed.
  Let PROOMD : pusage stD + 303104 <= B_PRIM. Proof. exact PROOM. Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 7430144 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 1 <= c <= 30 /\ CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c
            /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
            /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= cnt <= mc /\ 2 <= mc <= 16 /\ 1 <= n /\ n + n = mc /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384
            /\ 32 <= csz <= 65536 /\ RB s c <= p /\ p + csz <= RB s c + au /\ csz * (nf + cnt) <= au /\ TH mod 16 = 0 /\ sb mod 65536 = 0 /\ p mod 16 = 0 /\ mfa mod 262144 = 0
            /\ p = RB s c + idx * csz /\ 0 <= idx /\ U = p + rz /\ mch = U - 16 /\ 16 <= rz /\ rz mod 16 = 0 /\ 1 <= nu /\ U + round_up nu 8 <= p + csz
            /\ csz mod 32 = 0 /\ 8 * (round_up nu 8 / 8) = round_up nu 8 /\ nu <= round_up nu 8 /\ ch_end ch = p + csz.
  Proof.
    clear AX AMX DEP DPL MI ST PROOM OK VISE CBC AMXD PROOMD.
    placed. fold TH CTX sb in T1, T2, T3, X2, X3, S1, S2, S3.
    apply akobj_env in T2; [| unfold kPageSize; clear; tlia]. apply aapp_env in X2; [| clear; tlia].
    pose proof (cd_pure sD m _ _ c RQD HC INIT) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
    change (a_st sD) with stD in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    change (get_region stD c) with r in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11. change (get_pc stD c) with pc in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    fold nf mfa au mu fl cnt chunks csz mc in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    npose (class_size_table_facts c HCC) as (_ & C2 & _ & _ & _ & C6). fold mc in C6. fold csz in C2.
    pose proof (class_slots_count st _ _ c WQ HCC ltac:(clear - U10; fold csz; tlia)) as CNTB. fold r pc csz au fl chunks in CNTB.
    pose proof (ro_numfreed _ _ (WFQ_region st _ _ c WQ HCC)) as NFE. fold r nf fl in NFE. rewrite <- NFE, <- U8 in CNTB.
    npose GEOM as (_ & _ & _ & _ & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14). fold c p csz U mch in G5, G6, G7, G8, G9, G10, G11, G12, G13, G14.
    change (region_beg st c) with (RB s c) in G5, G6, G8, G14. fold st r au mu in G6, G7. change (ch_rz ch) with rz in G11, G12.
    pose proof (record_extQ s _ _ OKQ ch CHIN) as (_ & _ & _ & _ & _ & _ & X7 & _ & X9). fold U nu in X7, X9.
    pose proof (chunk_alignQ s _ _ OKQ ch CHIN) as (_ & A2' & _). fold rz in A2'.
    assert (EE : ch_end ch = p + csz) by (unfold ch_end; rewrite PRIM; reflexivity). rewrite EE in X7.
    assert (GEO : CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { unfold P, CA, RI, TH, sb, a_cache, a_ri, OT_CACHE, kSpaceSize, RB, FA, a_sb. rewrite free_array_base_eq, region_beg_eq. unfold kFreeArrayOffset. repeat split; reflexivity. }
    npose GEO as (_ & _ & _ & ERB & _).
    assert (NN : 1 <= n /\ n + n = mc) by (unfold n; clear - U11 C6; Z.div_mod_to_equations; tlia).
    assert (P16 : p mod 16 = 0) by (clear - ERB S1 C2 U10 G8; Z.div_mod_to_equations; nia).
    assert (T16 : TH mod 16 = 0) by (clear - T1; unfold kPageSize in T1; Z.div_mod_to_equations; tlia).
    assert (IDX : p = RB s c + idx * csz /\ 0 <= idx).
    { unfold idx. pose proof (Z.div_mod (p - RB s c) csz ltac:(clear - U10; tlia)) as DM. rewrite G8, Z.add_0_r in DM.
      split; [clear - DM; tlia| apply Z.div_pos; clear - G5 U10; tlia]. }
    assert (RU : 8 * (round_up nu 8 / 8) = round_up nu 8 /\ nu <= round_up nu 8) by (clear; unfold round_up; Z.div_mod_to_equations; tlia).
    unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kChunkHeaderSize in *.
    clear - LO T2 X2 S1 S2 S3 HC GEO U1 U2 U3 U4 U5 U9 U10 U11 NN G5 G6 CNTB P16 T16 IDX G10 G11 G12 A2' X7 X9 C2 RU EE.
    repeat match goal with |- _ /\ _ => split end; tlia.
  Qed.

  Theorem recycle_prim_arepq : ltac2:(zQ "70!klf!kq3!ku5!li6!jje!jnd!lj7>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
  Proof.
    (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay that
       destructured amaps_in_ledger at its PRE-RESTATEMENT shape; its first error was As:164 /
       Bs:165 "Illegal application: and_elimF6" over the old six-conjunct body, whose first
       conjunct this series guards by a non-zero ledger-word size (As//Bs AllocRep.v).  Written
       out as plain text; the STATEMENT IS UNCHANGED (still the encoded one above).  Shape from
       a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/
       AG_RecyclePrim.v:169-475, the same theorem in a section of the same signature.
       RULE 17: the donor's three tree-specific numbers -- 7704984, 11899304 and 7639432, its
       own depot base, depot map and side-buffer base -- are NOT carried.  RAV below carries
       this tree's own three, read off this tree's own As//Bs AsDepotInv.v:25-28, so the two
       twins differ in exactly those three numbers and nowhere else.  They are written out
       rather than named because this Section already binds that file's first notation as a
       Hypothesis, which shadows it.  Everything else is symbolic or allocator geometry shared
       by both trees.  Two facts this tree states differently from the donor are marked where
       they occur. *)
    intros K. pose proof BND as B.
    pose proof B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & ECA & EP & ERI & ERB & EFA & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & C1 & V3 & V5 & CNTB & T16 & S16 & P16 & M18
                     & EPI & I0 & EU & EMCH & RZ16 & RZA & NU1 & URU & C32 & RU8 & RUN & EE).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0). destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    destruct AB0 as [AB0a AB0b].
    (* [comment removed for export] *)
    destruct (cd_cells_of_arepq sD m _ _ c RQD HC INIT) as (q0 & q1 & q2 & q3 & PC1 & PC2 & PC3 & PC4 & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    change (a_st sD) with stD in PC1, PC2, PC3, PC4, RIC, RIJ, EXH, RST, FARR, FAJ, USJ. change (a_thr sD) with TH in QST, TST, REN. change (a_cache sD) with CA in PC1, PC2, PC3, PC4.
    change (get_pc stD c) with pc in PC1, PC3, PC4. change (get_region stD c) with r in RIC, FARR, FAJ, USJ. cbv zeta in PC1.
    change (CA + PCLASS_SIZE * c) with P in PC1, PC2, PC3, PC4. change (a_ri sD) with (a_ri s) in RIC, RIJ, EXH, RST, REN. change (a_ri s + REGIONINFO_SIZE * c) with RI in RIC, RIJ, EXH, RST.
    change (FA sD c) with (FA s c) in FARR, FAJ. change (RB sD c) with (RB s c) in USJ. change (a_ctx sD) with CTX in REN. change (a_sb sD) with sb in REN.
    fold cnt chunks mc nf mfa au mu fl in PC1, PC3, PC4, RIC, FARR, FAJ, USJ.
    pose proof (cd_pure sD m _ _ c RQD HC INIT) as (_ & _ & U3 & _ & _ & U6 & U7 & U8 & _).
    change (a_st sD) with stD in U3, U6, U7, U8. change (get_region stD c) with r in U3, U6, U7. change (get_pc stD c) with pc in U8. fold nf mfa mu fl cnt chunks in U3, U6, U7, U8.
    (* [comment removed for export] *)
    pose proof MEM as (_ & _ & _ & _ & _ & _ & CH & _). pose proof (CH ch CHIN) as CR.
    destruct CR as ((b1 & actx & HD & Hb1 & Hb1') & LC & STQ & JR & PL' & PR' & _). rewrite QUAR in HD, STQ. destruct STQ as [JU SHU].
    fold U nu in HD, JU, SHU, JR, PR'. fold p rz in LC, PL', JR, PR'. change (ch_end ch) with (p + csz) in JR, PR' || rewrite EE in JR, PR'.
    unfold kChunkHeaderSize in HD, LC. fold U in LC.
    assert (B1' : b1 = 17 \/ b1 = 145) by (clear - Hb1 Hb1'; Z.div_mod_to_equations; tlia).   (* this tree's header byte has two forms, not the donor's four *)
    assert (NSH : Z.to_nat (nsh nu) = Z.to_nat (round_up nu 8 / 8)) by (f_equal; unfold nsh, round_up; clear; Z.div_mod_to_equations; tlia).
    rewrite NSH in SHU.
    (* [comment removed for export] *)
    assert (EM : mch = sb + c * 2 ^ 32 + idx * csz + rz - 16) by (clear - EPI EU EMCH ERB; tlia).
    pose proof VISE as VISE'. rewrite EM in VISE'.
    eapply (recycle_prim_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo sb c TH CTX ATSD cb idx rz nu actx b1 cnt mc csz chunks q0 q1 q2 q3 nf mfa au mu fl).
    { exact LO. }
    { exact HI. }
    { exact SPT. }
    { constructor. exact SPA. }
    { exact HC'. }
    { unfold AHI_LO, kSpaceSize, kPageSize. clear - B6 B7. tlia. }
    { constructor. exact S16. }
    { rewrite TP. unfold wz, ATP, AIMG_TOP. clear; tlia. }
    { placed. unfold ATSD, AIMG_TOP. fold TH CTX in T2, T3, X2, X3. unfold kPageSize in T2. clear - B T2 T3 X2 X3. repeat match goal with |- _ /\ _ => split end; first [assumption | tlia]. }
    { constructor. exact T16. }
    { constructor. placed. fold TH CTX sb in D2, D3, TCX. destruct TCX as (TCX & _). unfold disj, kSpaceSize, kPageSize in *. clear - D2 D3 TCX. tlia. }
    { unfold kFreeArrayOffset, kUserMapSize. clear - EPI I0 V5 N8 N9. split; [exact I0|]. nia. }
    { constructor. exact RZA. }
    { clear - NU1 URU EU. tlia. }
    { exact B1'. }
    { exact CBR. }
    { clear - N5. tlia. }
    { exact U8. }
    { exact N4. }
    { fold n. assert (NC : 32 * (nf + cnt) <= 3758096384) by (clear - CNTB C1 N1 N4 N8 N9; nia). unfold kFreeArraySize. clear - N1 N2 N3 N4 N5 N6 N7 NC. tlia. }
    { constructor. unfold kFreeArrayMapSize. exact M18. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - N8 N9. tlia. }
    { exact U7. }
    { exact OK. }
    { exact VISE'. }
    { exact MI. }
    { exact ST. }
    { replace tp with (wz ATP); [exact REN| unfold wz; rewrite <- TP; apply Z_to_bv_bv_unsigned]. }
    { replace (TH + 208) with CA by (clear - ECA; tlia). exact CBC. }
    { replace (sb + c * 2 ^ 32 + idx * csz + rz - 16) with (U - 16) by (clear - EPI EU ERB; tlia). exact HD. }
    { destruct (Z.eq_dec rz 16) as [E16|NE]; [left; exact E16| right]. destruct LC as [E16|[MG _]]; [exfalso; exact (NE E16)|].
      split; [clear - NE RZ16 RZA; Z.div_mod_to_equations; tlia|].
      replace (sb + c * 2 ^ 32 + idx * csz) with p by (clear - EPI ERB; tlia). replace (p + rz - 16) with (U - 16) by (clear - EU; tlia). exact MG. }
    { fold csz. replace (sb + c * 2 ^ 32 + idx * csz + rz) with U by (clear - EPI EU ERB; tlia). exact SHU. }
    all: try (first [exact PC1 | exact PC2 | exact PC3 | exact PC4 | exact QST | exact TST]).
    all: try replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI by (unfold kSpaceSize, REGIONINFO_SIZE; clear - ERI; tlia).
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - ERB; tlia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - EFA; tlia).
    all: try (first [exact RIC | exact RST | exact FARR | exact FAJ]).
    { intros a kk Ha Hmc. exact (ak_resf_hi s mo AK a kk Ha Hmc). }
    { intros a kk Ha Hk. apply (ak_prim s mo AK a kk c HCC); [exact Ha| unfold kRegionSize; exact Hk]. }
    { exact NW. }
    { exact NWA. }
    { exact NOV. }
    { intros x Hx. apply (ak_zr_sb s mo AK). unfold kSpaceSize, kPageSize. fold sb. clear - Hx B6 B7 B8 ERB. tlia. }
    { exact (ak_zrsh s mo AK). }
    { exact (ak_lsh s mo AK). }
    { intros x Hx. exact (AWV x Hx). }
    { right; right. unfold ABUDGET, aPhi in AB0b. change (a_st s) with st in AB0b. unfold page_size in AB0b. clear - AB0a AB0b PROOM. tlia. }
    { exact (ak_atop s mo AK). }
    cbv beta. intros msF2 mo2 POST. lazy zeta in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & q2' & m' & L' & S' & POST).
    destruct POST as (OK2 & VIS2 & LED & MU & WM & MI2 & REN2 & ST2 & HDR' & MAG' & POIu' & PC1' & PC3' & PC4' & QST' & TST' & RI' & RST' & FARR' & FAJ' & POI').
    destruct LED as (EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG).
    rewrite Z.ltb_irrefl in EL, ES, VMN. rewrite Z.sub_diag, Z.add_0_r in EAG. cbn [app] in ES.
    (* [comment removed for export] *)
    change (cnt =? mc) with drained in EL, ES, VMN, EAG, MU, PC1', PC3', PC4', RI', FARR', FAJ', POI'.
    change (mc / 2) with n in EL, ES, VMN, EAG, MU, PC1', PC3', PC4', RI', FARR', FAJ', POI'.
    change (if drained then rta_mfa nf n mfa else mfa) with mfa' in EL, ES, VMN, EAG, MU, RI', FAJ', POI'.
    change (if drained then n else 0) with k in MU, PC1', PC3', PC4', RI', FARR', FAJ'.
    replace (RB s c + idx * csz + rz - 16) with (U - 16) in MU, HDR', MAG' by (clear - EPI EU; tlia).
    replace (RB s c + idx * csz + rz) with U in MU, POIu' by (clear - EPI EU; tlia).
    replace (RB s c + idx * csz) with p in MU, MAG', PC3' by (clear - EPI; tlia).
    replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI in MU, RI', RST' by (unfold kSpaceSize, REGIONINFO_SIZE; clear - ERI; tlia).
    change (TH + 208 + PCLASS_SIZE * c) with P in MU, PC1', PC3', PC4'. change (TH + 208) with CA in MU.
    change (Z.shiftr (p - RB s c) kCompactPtrScale) with (addr_to_compact st c p) in PC3'.
    (* [comment removed for export] *)
    assert (DR : if drained then cnt = mc else cnt < mc).
    { unfold drained. destruct (Z.eq_dec cnt mc) as [E|NE]; [rewrite (proj2 (Z.eqb_eq _ _) E); exact E| rewrite (proj2 (Z.eqb_neq _ _) NE); clear - NE N4; tlia]. }
    assert (NC : 32 * (nf + cnt) <= 3758096384) by (clear - CNTB C1 N1 N4 N8 N9; nia).
    assert (FROOM0 : efs_new (nf + n) <= kFreeArraySize).
    { unfold efs_new, round_up, kFreeArrayMapSize, kFreeArraySize. clear - B NC. Z.div_mod_to_equations. tlia. }
    pose proof (cd_state_fields stD XC XB c p drained WQD HC' INIT CLS DR FROOM0) as FLD. cbv zeta in FLD.
    change (get_pc stD c) with pc in FLD. change (get_region stD c) with r in FLD.
    fold cnt chunks nf mfa au mu fl mc n k in FLD. change (if drained then rta_mfa nf n mfa else mfa) with mfa' in FLD. fold st' in FLD.
    change (free_array_base stD c) with (FA s c) in FLD. change (addr_to_compact stD c p) with (addr_to_compact st c p) in FLD.
    destruct FLD as (Fpc_c & Fpc_o & Frg_c & Frg_o & Fmaps & Fsb & Fpa & Fsec & Fch & Ftq & Fgq & Fnr & Fci & Fii & Fqx & Fqn & Fqc).
    pose proof (WFQ_cd_state stD XC XB c p drained WQD HC' INIT CLS DR FROOM0) as WQ'. fold st' in WQ'.
    set (sA := mkAst st' TH CTX (a_fsb s) L' S' (a_Zr s) (a_AL s) (a_top s) (a_bot s)).
    pose proof (kr_of_flag drained cnt mc n nf mfa k mfa' eq_refl eq_refl eq_refl DR) as KR.
    pose proof (froom_of_flag drained n nf mfa mfa' eq_refl ltac:(unfold kFreeArraySize; exact N3) FROOM0) as FROOM.
    assert (KB2 : 0 <= k <= cnt /\ mfa <= mfa' <= 536870912).
    { unfold kFreeArraySize in FROOM. revert FROOM. pose proof KR as KR'. fold mc in KR'. fold n in KR'. destruct KR' as [(-> & -> & _)|(-> & E & ->)]; [clear - B; intros; tlia|].
      unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (Z.leb_spec (4 * (nf + n)) mfa) as [LE|GT]; [clear - B E; intros; tlia|]. clear - B E GT. intros FROOM. Z.div_mod_to_equations; tlia. }
    assert (SB2 : sh sb <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh (sb + 2 ^ 37 + 4096)
                  /\ sh p + rz / 8 = sh U /\ sh U + round_up nu 8 / 8 = sh (U + round_up nu 8) /\ sh (U + round_up nu 8) + (p + csz - (U + round_up nu 8)) / 8 = sh p + csz / 8
                  /\ 0x2008fff7000 <= sh p /\ sh p + csz / 8 <= sh (sb + 2 ^ 37) /\ sh (sb + 2 ^ 37 + 4096) < 0x10007fff8000 /\ sb <= p
                  /\ sh p + csz / 8 < 0x10007fff8000 /\ p + csz <= sb + 2 ^ 37 /\ 0x2008fff7000 <= sh sb /\ sh sb <= sh p /\ sh p + csz / 8 <= sh (sb + 2 ^ 37 + 4096)).
    { unfold sh, ASHADOW_BASE. change (2 ^ 37) with 137438953472. acb. clear - B KB2 ACEILB.
      repeat match goal with |- _ /\ _ => split end; Z.div_mod_to_equations; tlia. }
    pose proof (munch_agree _ _ _ MU) as AGW.
    set (W2D := lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa' ++ [(p, p + csz); (sh p, sh p + csz / 8)]) in *.
    set (Wtot := rp_W lo (bv_unsigned sp) p (U - 16) U nu TH ++ lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa') in *.
    (* [comment removed for export] *)
    assert (SUB : forall a, outside W2D a -> outside Wtot a).
    { intros a Ha. subst W2D Wtot. unfold rp_W, lcd_W in *. cbn [outside app] in Ha |- *.
      destruct Ha as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & _).
      repeat match goal with |- _ /\ _ => split end; try exact I;
        first [ assumption | clear - H11 B; fastlia | clear - H11 B SB2; fastlia | clear - H12 B SB2; fastlia | clear - H10 B; fastlia
              | clear - H11 B; tlia | clear - H11 B SB2; tlia | clear - H12 B SB2; tlia | clear - H10 B; tlia ]. }
    assert (AG2 : agree_on (outside W2D) m m') by (intros a Ha; apply AGW; exact (SUB a Ha)).
    (* [comment removed for export] *)
    assert (ZS : forall a, (p <= a < p + csz \/ sh p <= a < sh p + csz / 8) -> ~ (p <= a < p + 8) -> ~ (U - 16 <= a < U - 12) -> ~ (sh U <= a < sh U + round_up nu 8 / 8) -> outside Wtot a).
    { intros a Ha N1' N2' N3'. pose proof (ZC_slotW sD m XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO a Ha) as ZW.
      subst Wtot. unfold rp_W. cbn [outside app]. placed. pose proof (akobj_lit _ _ T2) as BT. unfold kPageSize in BT. fold TH in BT.
      pose proof (carved_vs_threadQ s _ _ OKQ _ _ CV) as CT. fold TH csz in CT. unfold kPageSize in CT.
      split; [clear - Ha B SB2; tlia|]. split; [exact N1'|]. split; [clear - N2'; tlia|]. split; [exact N3'|]. split; [| exact ZW].
      destruct Ha as [Ha|Ha]; [clear - Ha CT B; tlia| clear - Ha BT SB2 B; tlia]. }
    assert (JK2 : junk m' p csz).
    { intros _. pose proof (stk_of_rw_cells asegs _ _ _ HDR') as S2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in S2.
      assert (S3 : stk asegs m' U (U + nu)).
      { eapply (stk_transport_pt (outside Wtot) m m' AGW WM); [exact (JU ltac:(clear - NU1; tlia))|]. intros a Ha. apply ZS; clear - Ha B SB2; tlia. }
      assert (S4 : stk asegs m' (U + nu) (p + csz)).
      { destruct (Z.lt_ge_cases (U + nu) (p + csz)) as [LT|GE].
        - eapply (stk_transport_pt (outside Wtot) m m' AGW WM); [| intros a Ha; apply ZS; clear - Ha B SB2; tlia].
          replace (p + csz) with (U + nu + (p + csz - (U + nu))) by (clear; tlia). apply JR. clear - LT; tlia.
        - split; [clear - B; tlia|]. split; [clear - B GE SB2; acb; tlia|]. intros a Ha. exfalso. clear - Ha GE. tlia. }
      assert (S1 : stk asegs m' p (U - 16)).
      { destruct MAG' as [E16|[GE MG]].
        - split; [clear - B SB2; tlia|]. split; [clear - B SB2 E16; acb; tlia|]. intros a Ha. exfalso. clear - Ha E16 B; tlia.
        - pose proof (stk_of_rw_cells asegs _ _ _ MG) as S0. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in S0.
          destruct (Z.lt_ge_cases (p + 16) (U - 16)) as [LT|GE2].
          + eapply stk_merge; [exact S0| | clear - LT; tlia].
            eapply (stk_transport_pt (outside Wtot) m m' AGW WM); [| intros a Ha; apply ZS; clear - Ha B SB2; tlia].
            destruct LC as [E16|[_ JK0]]; [exfalso; clear - E16 GE; tlia|]. replace (U - 16) with (p + 16 + (rz - 32)) by (clear - B; tlia). apply JK0. clear - LT B; tlia.
          + replace (U - 16) with (p + 16) by (clear - GE GE2 B; tlia). exact S0. }
      eapply stk_merge; [exact S1| | clear - B; tlia]. eapply stk_merge; [exact S2| | clear - B NU1; tlia].
      replace (U - 16 + 16) with U by (clear; tlia). eapply stk_merge; [exact S3| exact S4| clear - B NU1; tlia]. }
    assert (PS2 : poisoned m' p (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic).
    { pose proof SB2 as (_ & _ & E1 & E2 & E3 & _).
      replace (Z.to_nat (csz / 8)) with (Z.to_nat (rz / 8) + (Z.to_nat (round_up nu 8 / 8) + Z.to_nat ((p + csz - (U + round_up nu 8)) / 8)))%nat
        by (clear - B; Z.div_mod_to_equations; tlia).
      apply poisoned_app.
      - eapply (poisoned_transport_pt (outside Wtot) m m' AGW WM); [exact PL'|]. intros a Ha. rewrite Z2Nat.id in Ha by (clear - B; Z.div_mod_to_equations; tlia).
        apply ZS; clear - Ha B SB2 E1; tlia.
      - rewrite Z2Nat.id by (clear - B; Z.div_mod_to_equations; tlia). replace (p + 8 * (rz / 8)) with U by (clear - B; Z.div_mod_to_equations; tlia).
        apply poisoned_app; [exact POIu'|]. rewrite Z2Nat.id by (clear - B; Z.div_mod_to_equations; tlia). rewrite RU8.
        eapply (poisoned_transport_pt (outside Wtot) m m' AGW WM); [exact PR'|]. intros a Ha. rewrite Z2Nat.id in Ha by (clear - B; Z.div_mod_to_equations; tlia).
        apply ZS; clear - Ha B SB2 E1 E2 E3; tlia. }
    (* [comment removed for export] *)
    assert (R2 : AREPQ sA XC XB m').
    { eapply (arepq_after_cd sD m m' XC XB c p st' L' S' (a_AL s) lo (bv_unsigned sp) q0 q1 q2' q3 k mfa');
        first [exact RQD| exact HC'| exact INIT| exact CLS| exact KR| exact FROOM| exact WQ'| exact LO| exact AG2| exact WM| exact JK2| exact PS2| eassumption| idtac]. all: fail "R2". }
    assert (AWV2 : awin_vis sA m').
    { exact (awin_after_cd sD m m' XC XB c p st' L' S' (a_AL s) lo k mfa' RQD HC' INIT CLS KR FROOM ES LO WM POI' AWV). }
    assert (FX2 : flagsx_rep m').
    { exact (flagsx_after_cd sD m m' XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO AG2 WM FXR). }
    assert (AMX2 : AMODELX sA mo2).
    { eapply (amodelx_after_cd sD mo mo2 XC (p :: XB) c st' L' S' (a_AL s) k mfa' (firstn (Z.to_nat k) chunks ++ fl));
        first [exact AMXD| exact PL| exact WQD| exact HC| idtac].
      all: try first [exact FROOM| exact Fsb| exact Fpa| exact Fsec| exact Frg_c| exact Frg_o| exact Fmaps| exact EL| exact ES| exact VMM| exact VMR| exact VML| exact VMB| exact VMN| exact EAG].
      - destruct KR as [(K0 & M0 & _)|(Kn & _ & Mn)]; [left; exact (conj K0 M0)| right; exact (conj Kn Mn)].
      - exact (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK)).
      - exact (nonvm_same_atop _ _ NVS).
      - change (a_AL sD) with (a_AL s). clear - AB0a. tlia. }
    (* [comment removed for export] *)
    assert (DEP2 : DEPOT asegs d m').
    { eapply (DEPOT_transport asegs d m m' _ DEP MU WM).
      pose proof (depot_avoid_cd sD m XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO d DPL) as DAV.
      assert (XD := carved_vs_depotQ sD _ _ OKQD _ _ CV d DPL). fold csz in XD.
      pose proof DPL as (G1 & G2 & G3 & G4 & _ & _ & _ & _ & _ & Nd1 & Nd2 & Nd3 & Nd4). fold TH in G1, G2. fold sb in G3, G4.
      pose proof (aapp_lit _ _ Nd1) as L1. pose proof (aapp_lit _ _ Nd3) as L3. apply aapp_env in Nd1; [| clear; tlia]. apply aapp_env in Nd3; [| clear; tlia].
      placed. pose proof (akobj_lit _ _ T2) as BT. unfold kPageSize in BT. fold TH in BT.
      subst Wtot W2D. unfold depot_avoid, avoids, rp_W, lcd_W. cbn [app]. unfold disj, kPageSize, kSpaceSize in G1, G2, G3, G4. acb.
      clear - B KB2 BT G1 G2 G3 G4 Nd1 Nd2 Nd3 Nd4 L1 L3 SB2 XD ACEILB B1 EP ECA B8 N4 N5 ERI EFA ERB N1 N2 EU RZ16 URU RUN NU1 C1 B6 B7.
      set (RAV := fun x y : Z => (y <= 2760984 \/ 6955304 + 8 <= x) /\ (y <= 2695432 \/ 2695432 + 28 <= x)
                                 /\ (y <= d_nb d \/ d_nb d + 16 * 65536 <= x) /\ (y <= d_sb d \/ d_sb d + 8 * 32768 <= x)).
      assert (A_stk : forall x y, aceil <= x -> RAV x y) by (intros x y Hx; subst RAV; cbv beta; clear - Hx Nd2 Nd4 ACEILB B6 B7; tlia).
      assert (A_thr : forall x y, TH <= x -> y <= TH + 4096 -> RAV x y) by (intros x y Hx Hy; subst RAV; cbv beta; clear - Hx Hy BT G1 G2; tlia).
      assert (A_spc : forall x y, sb <= x -> y <= sb + 137438953472 + 4096 -> RAV x y) by (intros x y Hx Hy; subst RAV; cbv beta; clear - Hx Hy G3 G4 B6; tlia).
      assert (A_sh : forall x y, 0x2008fff7000 <= x -> y <= 0x10007fff8000 -> RAV x y) by (intros x y Hx Hy; subst RAV; cbv beta; clear - Hx Hy L1 L3 Nd1 Nd3; tlia).
      assert (A_slot : forall x y, p <= x -> y <= p + csz -> RAV x y) by (intros x y Hx Hy; subst RAV; cbv beta; clear - Hx Hy XD SB2 B6; tlia).
      assert (ALL : Forall (fun iv => RAV (fst iv) (snd iv))
                      ((lo, bv_unsigned sp) :: (p, p + 8) :: (U - 16, U - 16 + 4) :: (sh U, sh U + round_up nu 8 / 8) :: (TH + 2840, TH + 2856)
                       :: (lo, bv_unsigned sp) :: (P, P + 4) :: (P + 16 + 4 * (cnt - k), P + 20 + 4 * (cnt - k)) :: (CA + 2576, CA + 2584)
                       :: (RI, RI + 8) :: (RI + 16, RI + 32) :: (RI + 80, RI + 88) :: (FA s c + 4 * nf, FA s c + mfa')
                       :: (sh (FA s c + mfa), sh (FA s c + mfa) + (mfa' - mfa) / 8) :: (TH + 2800, TH + 3168) :: nil)).
      { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
          first [ apply A_stk; clear - B1; fastlia                       (* [comment removed for export] *)
                | apply A_slot; clear - EU RZ16 URU RUN NU1 C1; fastlia
                | apply A_sh; clear - SB2 KB2; fastlia
                | apply A_thr; clear - EP ECA B8 KB2 N4 N5; fastlia
                | apply A_spc; clear - ERI EFA ERB B8 N1 N2 KB2; fastlia
                | apply A_stk; clear - B1; tlia
                | apply A_slot; clear - EU RZ16 URU RUN NU1 C1; tlia
                | apply A_sh; clear - SB2 KB2; tlia
                | apply A_sh; clear - SB2 RZ16 URU RUN NU1; Z.div_mod_to_equations; tlia
                | apply A_thr; clear - EP ECA B8 KB2 N4 N5; tlia
                | apply A_spc; clear - ERI EFA ERB B8 N1 N2 KB2; tlia ]. }
      split; [| split; [| split]].
      - eapply Forall_impl; [| exact ALL]. subst RAV. cbv beta. intros iv (H1 & H2 & H3 & H4). exact H1.
      - eapply Forall_impl; [| exact ALL]. subst RAV. cbv beta. intros iv (H1 & H2 & H3 & H4). exact H2.
      - eapply Forall_impl; [| exact ALL]. subst RAV. cbv beta. intros iv (H1 & H2 & H3 & H4). exact H3.
      - eapply Forall_impl; [| exact ALL]. subst RAV. cbv beta. intros iv (H1 & H2 & H3 & H4). exact H4. }
    (* [comment removed for export] *)
    assert (MODEL : rp_model st').
    { intros stA SBS.
      assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
      { intros a Ha Hb. apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. acb. clear - Ha Hb B ACEILB. tlia. }
      destruct (cb_recycle_prim_eval stA st XC XB ch SBS WQ CHIN PRIM QUAR INIT) as (stA' & ev & EV & SB').
      - fold U nu. split; [| split]; [change 7 with (Z.ones 3); rewrite Z.land_ones by (clear - B; tlia); change (2 ^ 3) with 8; clear - B P16; Z.div_mod_to_equations; tlia| apply IM; clear - B; tlia| apply IM; clear - B NU1 RUN; tlia].
      - fold c. intros _. exact FROOM0.
      - fold c. cbv zeta. intros DT GT. fold r in GT |- *. fold nf mfa mc in GT |- *. fold n in GT |- *. change (free_array_base st c) with (FA s c).
        assert (E1 : efs_new (nf + n) = mfa + 262144).
        { unfold efs_new, round_up, kFreeArrayMapSize. clear - B GT NC. Z.div_mod_to_equations. tlia. }
        rewrite E1. split; [| split; [| split]].
        + change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - B; tlia). change (2 ^ 3) with 8. clear - B M18. Z.div_mod_to_equations. tlia.
        + apply IM; clear - B; tlia.
        + change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - B; tlia). change (2 ^ 3) with 8. clear - B M18. Z.div_mod_to_equations. tlia.
        + apply IM; clear - B; tlia.
      - exists stA', ev. split; [exact EV|]. exact SB'. }
    apply K. unfold rp_gpost, rstep_post.
    exists sA, t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    repeat match goal with |- _ /\ _ => split end; try reflexivity.
    - cbn [a_sb a_st]. unfold a_sb. cbn [a_st]. exact Fsb.
    - unfold a_pa. cbn [a_st]. exact Fpa.
    - intros sc Hsc. cbn [a_st] in Hsc. rewrite Fsec in Hsc. exact Hsc.
    - exact Fci.
    - intros c0 H0. cbn [a_st]. destruct (Z.eq_dec c0 c) as [->|NE]; [rewrite Frg_c; reflexivity| rewrite (Frg_o c0 H0 NE); reflexivity].
    - exact OK2.
    - exact VIS2.
    - exact R2.
    - exact AWV2.
    - exact FX2.
    - exact AMX2.
    - exact NVS.
    - apply avmx_same; [exact VMM| cbn [a_st]; exact Fsec].
    - unfold depot_cov in DCOV |- *. rewrite VMM. exact DCOV.
    - exact DEP2.
    - unfold depot_placed in DPL |- *. cbn [a_thr a_sb a_ctx a_pa a_st]. unfold a_sb, a_pa in DPL |- *. cbn [a_st]. rewrite Fsb, Fpa, Fsec. exact DPL.
    - exact MI2.
    - exact ST2.
    - (* [comment removed for export] *)
      apply (acompl_of_munch s sA d lo (bv_unsigned sp) _ m m' MU). intros iv a Hiv Ha.
      unfold rp_W, lcd_W in Hiv. unfold awrit. change (a_thr s) with TH. change (a_sb s) with sb.
      apply in_app_iff in Hiv.
      destruct Hiv as [[<-|[<-|[<-|[<-|[<-|[]]]]]]|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; cbn [fst snd] in Ha; unfold kPageSize, kSpaceSize;
        first [ left; exact Ha
              | right; left; clear - Ha B KB2; fastlia                      (* [comment removed for export] *)
              | right; right; left; clear - Ha B KB2 SB2; fastlia
              | right; right; right; left; clear - Ha B KB2 SB2; fastlia
              | right; left; clear - Ha B KB2; tlia
              | right; right; left; clear - Ha B KB2 SB2; tlia
              | right; right; right; left; clear - Ha B KB2 SB2; tlia ].
    - apply avis_of_wmono. exact WM.
    - (* [comment removed for export] *)
      intros a (x & Hx & Ha). apply AG2. pose proof (WFQ_xb stD _ _ x WQD ltac:(right; exact Hx)) as CVx. unfold xb_ok in CVx.
      change (class_of_addr stD x) with (class_of_addr st x) in CVx.
      assert (NE : x <> p).
      { intros E. pose proof (NoDup_app_r _ _ (WFQ_carved stD _ _ WQD)) as ND. inversion ND as [|y l NI ND' EE2]. subst y l. apply NI. rewrite <- E. exact Hx. }
      destruct Ha as [Ha|Ha].
      + exact (ZC_carved sD m XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO _ _ a CVx NE Ha).
      + pose proof (carved_in_spaceQ sD _ _ OKQD _ _ CVx) as (Y1 & Y2 & Y3). pose proof (class_size_table_facts (class_of_addr st x) (proj1 CVx)) as (_ & C8 & _).
        assert (X8 : x mod 8 = 0).
        { destruct CVx as (_ & _ & _ & V4 & _). rewrite region_beg_eq in V4. change (as_space_beg stD) with sb in V4.
          apply Z.mod_divide in V4; [| clear - Y3; tlia]. apply Z.mod_divide in C8; [| clear; tlia].
          assert (D8 : (8 | sb)) by (destruct (proj1 (Z.mod_divide sb 65536 ltac:(clear; tlia)) S16) as [kk Hk]; exists (kk * 8192); clear - Hk; tlia).
          apply Z.mod_divide; [clear; tlia|]. replace x with ((x - (sb + class_of_addr st x * 2 ^ 32)) + (class_of_addr st x * 536870912) * 8 + sb) by (clear; tlia).
          apply Z.divide_add_r; [apply Z.divide_add_r; [| apply Z.divide_factor_r]| exact D8].
          eapply Z.divide_trans; [| exact V4]. eapply Z.divide_trans; [| exact C8]. exists 4. reflexivity. }
        apply (ZC_carved_sh sD m XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO _ _ x (class_size (class_of_addr st x) / 8) a CVx NE);
          [clear; tlia| | exact X8| | exact Ha]; clear - C8 Y3; Z.div_mod_to_equations; tlia.
    - (* [comment removed for export] *)
      intros ch0 H0 E0. cbn [a_st]. unfold chunk_list. rewrite Fch. apply (proj2 (del_in st ch KEYS CHIN ch0)). split; [exact H0|].
      intros EU0. assert (EQ : ch0 = ch) by (exact (WFQ_inj st _ _ WQ ch0 ch H0 CHIN EU0)). rewrite EQ, QUAR in E0. discriminate E0.
    - (* [comment removed for export] *)
      intros a (ch0 & H0 & E0 & Ha). apply AG2.
      assert (H0D : In ch0 (chunk_list stD)).
      { apply (proj2 (del_in st ch KEYS CHIN ch0)). split; [exact H0|]. intros EU0. assert (EQ : ch0 = ch) by (exact (WFQ_inj st _ _ WQ ch0 ch H0 CHIN EU0)). rewrite EQ, QUAR in E0. discriminate E0. }
      pose proof (record_extQ sD _ _ OKQD ch0 H0D) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). pose proof (chunk_alignQ sD _ _ OKQD ch0 H0D) as (_ & _ & A3 & _).
      assert (RU : ch_used ch0 <= round_up (ch_used ch0) 8 /\ 0 <= nsh (ch_used ch0) /\ 8 * nsh (ch_used ch0) = round_up (ch_used ch0) 8)
        by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; tlia).
      destruct Ha as [Ha|Ha].
      + apply (ZC_rec sD m XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO ch0 a H0D). clear - Ha X3 X6 X7 X8 RU. tlia.
      + apply (ZC_rec_sh sD m XC XB c p lo (bv_unsigned sp) k mfa' RQD HC' INIT CLS KR FROOM LO ch0 (ch_user_beg ch0) (nsh (ch_used ch0)) a H0D);
          [clear - X3 X6 X8; tlia| clear - X7 RU; tlia| clear - A3; Z.div_mod_to_equations; tlia| clear - RU; tlia| exact Ha].
    - exact MODEL.
  Qed.
End RPStep.
End HCW.
