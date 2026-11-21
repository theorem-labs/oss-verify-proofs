(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach AllocSim MmapSim LazyRestrict LazyLedger LazySR LazyNodes AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepFacts2 AllocRepX
     AsDepotInv AW_DepotFrame AllocWalkKit AW_Efs SecLazy AS_Refill1 AS_Refill2 AS_Rta AS_LcDealloc AG_Malloc AG_Malloc2 AG_MallocModel AG_ColdModel
     AG_Refill3 AG_MallocCold AG_RepQ AG_RepQFacts AG_RepQFacts2 AS_Free2 AG_RecycleModel AG_CacheDealloc0 AG_CacheDealloc1 AG_CacheDealloc2
     AG_WriteSet AG_RecycleDefs AllocTacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import PerfLia.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_CacheDealloc3 () := KReplay.lz_vm "#&B^C47Corelib7Classes9Morphisms6Proper!sI?:forall_def!sM?Krespectful_per_obligation_1C46Stdlib5Lists4!s+#8nil_cons!s{,4Init5Logic6eq_indK!t?,Numbers7BinNums8positive02!sK=1Z02C5!tJ&6ZArith6BinInt1Z2le!sB<3add!sC=mul!tgG1K!um'9micromega=RingM!s4'5Psatz!u8#!sOI7K!vJ19Datatypes3nat!sn8:Z!sk+;!u>%Proof!sRP3!tE<4list!u_#!sF@2I!sFA0!tZ66VarMap1!uL9!sD,1!sD@3I!sD?0I!w>C7Formula!tq87Env!sT#5PExpr!tX8!sI22!vG<6op!|9#!uc8!sk23!sIE5C!sI55Tauto8B!uH&K!}+72eq01C!y/@=Z!sn$CheckerI!sl;0C!w?<4find!t3AC!t30_sou!~i#!|2I5!sOK6K!xlL!xI7!vn&G!sJ'4!sJF8I!#4Y>0!t_D3Op203!xK<5eKind!|{=uni!|{9!se%4kind!~'?!sf$1!#5QF3!#7:?1I!xl@!#4&/0!#5I@1!#4uM1!v8=bool!t9>!sF%1I!#8`&5FSets<FMapP!ui&;!s/'!{H#tree!{i#!|'68!#:w$_rC89OSSVerify6!to$s:boost_json:fuzz_parse3lib3Lib2Nd;ex_introF17C13~~~!slP2As6AS_Rta7rta_mfa!sk&!#;0;div!#<-=t!~]83and00!~x9or!w+4!s[-1K!s[;2!s@<1!uxUW_Efs7efs_new!uxClebC7!t0N>AsanAllocModel>kFreeArraySize!w{Y7AG_RepQ<AREPQ_placed!sqa9!sq%WFQ!snY8!uY$Rep9!t\%_ok!t_a3!tY+!#6FE5!#6$H5!x$_;kNum!#Fd%!uQ&!st^=c!sp#_of_addr!w:_Kit6carv!xp+!v%'!#H&,2In!wN[6WFQ_xb!y+b4a_s!sj\sShadow5aceil!tWepa!tWb4aapp!tVb5a_thr!skdkobj!tXectx!vucdis!tWffs!z#gt!}Ue6as_sec!soe:sc_map_beg!sse;!ss&s!#90+!#<&7not!zW`o!{D'!#;L;pow!t0_bot!xVb2RB!shcFA!u\B6modulo!t0\9!}U$_env!tyb8aapp!sn]@AG_CacheDea!sx#07cd_pure!{Efget_region!sse<rg_num_fre!#:k'!su^Drg!|<#ped!sx$_array!s}eArg_!ve$ated_user!sze>!ty,!swi=rg!uk5!#L<:6length!{n=to_nat!#6N_!y>#p!#6Ne8pc_coun!#82e9!sq#hunk!#CUe4zle!{hf9max!uUk:!#E8$s!#K+[!#3=3A!sx&lots!tt0!t#R!#E1&:WFQ!#3C0!soT!tf#Wf;ro_num!#3>i:!ta%!#=I,!#;M;su!#Os_<as_space!t:-!#8rWKit=!u+,_eq!u|e?!#3E+_base!tmbB!su2!tr,!v{;7div_mo!#k=<=mod_pos_boun!sMBneg!sM25!#O}#8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL3!u14compare!#^3?!#f5>3Pol!#gf?!sG$!shD2!#Gm^ri!xa_Rep7a_cach!#F$'!tz49SatDivModCZ_!wD#non!wo#!s,%!v|<>pow!xf$!sNB:!sN#!sJ&!tKB!y9$!tK/!x$>N!#kZF7!vTP!#`\%:and_elimF5!#5f`F!#8I+_table_facts!s{V!th46!sk%!#Z2E3!sJF7!#kbJ4!w9E4!#[JH1!{6U!#UM%6AHI_LO!#9WekSpace!#a6,!#>q^kPag!srj@kPtr!#bz#Reserve!~`b8AFS_SIZE!sn%I!#Do^s!#C1#00!u\eA!#eY+Map!vXi<kUser!sul@!tq,Offse!#BG%I!#oa?!#k%85False!sC4!sb,:!#:K$ison!si:4Tru!sh$5stdpp9bitvector;definitions2bv!t3>!#zm&0C!sk@;bv_unsigned!z4S<AS_Lc!#F&%5lcd_W!#5GY5Frame5munch!{hY>!{h'Facts2;!sq$_agre!y3'!#:S:8eqb_spec!#EK<eqb!w-<7reflect00!#Idc8cd_state!vd`7outsid!#3Pc!vZ$_!#JG&c!uSb38nc!#D>%!|gA4prod!vkU!#9&'2sh!up[S_!~b#2;!v_&_!#hB+!~E8proj1!ym=le!ym%!u`<8BoolSpec!udU>!#O6#cycleDefs5pendz!#5[U8HeapCeil5h!#lX^!wA&;!#mE#!#A0[2As9!z<'X@sh_!st#ing_rang!{z[3Mem2w!#n>Y!#S=&5xb!#v\]!#DP$@!#s8$!#t'#_lis!#Txf!#t3/!soR=!#6//;NoDup!{X#_r!}W'!{?&!#u',5!sL$!$&599!#;=#_!$2x#!sE67f_equal!#5|b19ZC!uo`<!v`&!un$!w\'in!#Um$!#|z&!#`#;divid!$?\<:mod_!sJ&!ziS9LiaTuning9zify_don!{\&!#I&J3!$8a9x!#HRT!w=4<!w=+_!#6`W!#LF33!skg2!sk]9ex!sj%1!w''!#:0?1!#fK;3app!whK1!txT!#=k$3iv!#7D%!#II_a!#?E#!#II&!$6'A!$1h8!#Eq$1!tU`!#^w$!tU'!sq`p!#T##!sq+!{f;0!#@Ndcd_gpo!#7^&K4ELinuxProcessSemantics?!s<23Run6config!yY#!#HY>D!#HY,_in!#;=%!sY@:b!#`?#ulus!#<Y\8awin_vi!#=Jc:flagsx_rep!sqc7AMODELX!snY!#FC'6!sm%!t\dakerne!$/0b?amaps!xI#ledger!suds!#BU#!x%#ibl!#Igb7ABUDGET!sm&!}K^7as_!u`#!spfmp_ki!#JR&K!sp^5m!$GA#3!spl4!uTi!#lW,!~H@7Z_to_bv!t>c!$-G-!#4pH5State8m_vm!xC$!s]P7vm_!s\U;vm_noac!s;#!ugP<LazyRestrict:!#6B&!$4Qc3a_L!x]V:!t\#L!~I$9nooverlap!sna>entries_nowra!$:qb4a_A!uOW!w,1eager_us!#H_Z!w,/S!t\c;pages_tota!$?_dPhi!|:Xvm_limi!$7yS!#~>5d_cell!$EM$repq!uJV3Lib4TacX2w!#Uz%K!#E[SC!tS#4!tY#02!sjf1!u=`b8!tQf!#7f%I!wiR:AS_Refill14RENV!#j='!}:^Zr!uFV!#R$#!sj#WalkKit6hidden!vy\6M!zz$C!#9^%_!#g>-!uXX!#DF,ak_resf_!|]Y<map_contains!#CK__prim!uDc8ak_zr!$M3[!t_1zr!#c5Z!sn,6ak_l!sm[;!sm$Budget6pusage!uNga!$Eh+!{;T!#mk,B!$$]#_d!s4%_!#N=+!#PBO6LazySR4lzo!#t}X!#9X/8r!s/&!|wZ!#U#%mkR!}`a6r!$=7-!skS8PropExec7seg_rom!t[a2MS!x]Y!#6N+29rf!#M/\!vx,5wmono!siZ3Mem7mem_i!$I1'!#aA;shiftr!ugS!#jL'8poiso!#6]+!#t+;ltb!#6/P=!#Pu#subtrac!#?kS7Sec!{V#:nonvm_sam!#JOW;vm_r!$$b$d!#8>Qvm_m!$T0#ase!saQ6vm_brk!#eu<ltb_irrefl!#qo<sub_dia!$4U<7ad!$9H#!$`F69app_nil_!t/=6eq_d!#rv36Specif7sum!$o1$!sf?b_eq!#tC<!%%g<7!sa#neq!y&S!#Eo3?!#zI&_field!#UAe?!#p##to_!$%S#!#6\&K!#aRe1!tke<as_ptr!$NZ/!w&'!$sPA1!$ND_9as!$L`k5as_tq!snig!snf=as_n!#3&+!yXfs!$@M$_init!sxg@as_internal!s{$!sye7as_qmax!spki!$Qzf!sp#!$D#,!}'`!#lJ%!#KMV!#3o6<!#{-#!$/>/K!#<`Sl!#V^&st!tg'!#l~c:kr_of_flag!sxj=froom!s{1!v^c18ZC!$UU#W!svY!vZ+Ajunk_transport_p!$g5b4!sw#!sj&!#;0;of!$]]#!sF24Znat5Z2Nat2id!tP\E!#B_&!uMf!w>4>!#ZL#_after_c!$~%a5!$~%#!thj=!#rM#!tga!s{4?!#rY%!s}2!#NdU;lzok!#f6%!slV9!sl#NodesFlazy!so&_okb!#da_!#G;&?!#G;+!#RB]!v]32@amodelx!w]s>depot_avoid!s|\=AW_D!sn#!#Mu#;!sy-!sv%!#FG+!#G-$7!s+#Def6F!%JT#!$2M93if!%Jk?:!%Jk+!sM?@subrel!%K+$!#IN#!sS>F!sS1!t-+!v/R:As!v-$Inv4d_n!#[OY!sl1!#\='!u5>I!$DY#xive_!s0,proxy!s\?B!uk/p!%OR%!#L#4:!wt%!$@C#!st4>!st+_Prop@and_iff_m!s=&!$7X8!sL$nd!z-a?DEPOT!#7I+!w3d5!sw$!smY>AG_Ma!#@{'?!~f$but_!#|x$!s{Y<!}l#old!sy$;in_mem_hig!#``&!#;d:4la!$ds=4ones!sD<9!sb#_!sI$!#3ja0=!#Oq'ev!#q&'!#J5^!#a&/!sv%!%MKC!$:>S;AG_WriteSet4avm!%/uY!#c|+9!#5n$cov!z`[!yq'2<!sq%!%={^!uU/6acompl!{X]!$JH,4a!$2F[!sp2:alive_ke!#BQZ!$L22!sv$!sq%!$7Sg!#=$#!wDe9!ys#!#_+-!sr^5awrit!sne?!y$%_of_!$Y%_!wG0=!y1#!sy#!#eV-!~f^:!#XF#!$LY-!ss^8ch!$Xi/!$Bj;s!$sw-!#Zx@8element!%cE,!#A703map!u'_;ch!%,3#!%9Ah7!st%!$''[!#i,%3n!#sqZ=!$MO-2;record_extQ!sv[!#6z%!sw$5ch_lo!uS[!sp&6ch_en!#\$e<ch!%39$!x&i!uS#rz!{mfround_up!x0g<!}W%align!#QSj6ZC_rec!stj9!st%!$Q#'!#8fgz!#Al#!toU!$PE%;!$Q2'!%Z_W!sl50!slh8!sl]:!$Rg'9!w~Y!#~1/D!#~10sreach!uYg3!$P=V6SR!tN#6!tU%0!w2[4Step8rw!$73$!sk&!#NC53rev!#4k[5w!$aMY!#{?#Arr6u32ar!#|l`3st!#`d%!%#3E6!#<$:5skipn!sD;6firstn!#hu^7mapping!#hv'!#>O;fst!#VQ?!#T8/per!#T?DNR!sY,artia!#S{#!#SR+!uM^>!#vC#i!$P2#me!$4YY!#JZ0stat!#R7Y5ASegs5aseg!#`YV4Scfg=hunspell_scf!#<8%I!zYT!$=N,!%#ue7PROT_RW!yQ37Program6Basics4imp!#\}?Diff_!sK#_!#ZA,I!$%#I>Riscv!sE+=machine_!$`0%I!$%nO5!uN$00I!|ag!$_}e!$S&%!$bF&!spe2!spl6!spl!#<a&!wpP9page!$T4$!#8vZ;PCLAS!%1]-!sq\?REGIONINFO!sug3ATP!sib4ATSD!#4]^8AIMG_TOP!#3-d;kR!#{S#!%rU\!$B</B_PRIM!tee@kC!$01$PtrSca!$a/&I!#Kf`!%7Q,!$kW_!$#o$!sq+!ya\ast!#8:fIk!s6#HeapLeftRedzoneMagi!#Kj&!#8-3?R!#7p%!s6&=iff_!#>1'!yfaHighMemB!%h%g!st'E!%/z'!w~_eff!%44$!}2^<ASHADOW_BAS!#3R[!#WN&!#A6'!uM`c!$uH0!sqf!#EH&!#\TI3key".
Local Ltac2 zQ s := CDef.cdeft "46Stdlib6ZArith6BinInt1Z02le37Corelib7Numbers7BinNumshc1Z03add03mul37Corelib4Init5Logick32eq37Corelib4Init9Datatypeslc4boolk33and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6AS_Rta~~~~~~o17rta_mfa03div02ltk32or69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~t5ekFreeArraySize79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As6AW_Efs~~~~~~hi77efs_newt56astatelc4listt56effectlc4prodk32ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_MallocModel~~~~~~hp3fsame_but_shadowlc4Somelc6optionlc4pairt5dcache_dealloc3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsih1dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Stateil95Model99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Ash0AG_CacheDealloc33HCW6CDStep~~~~~~ip08cd_model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAG_RecycleDefs~~~~~~iuearstep_post3h5LinuxProcessSemanticsfLinuxProcessSem3Runjk05mkCfg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~jn55asegs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~jr96sreach69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jvcdhunspell_scfgip08cd_gpost79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~kl04a_stlc4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AG_RepQ~~~~~~kpd5AREPQt5dclass_of_addrlc4truet5fas_cache_inited79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~lgc8awin_vislgcaflagsx_replgc7AMODELX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsDepotInv~~~~~~ln05DEPOT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAG_Malloc2~~~~~~lr9cdepot_placedlgc9depot_cov79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mh67mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~mlb5aceilhc4Npos35stdpp9bitvectorbdefinitionsmq9bbv_unsigned03pow06modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~mu23stkkl03ATP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAllocBudget~~~~~~nic6B_PRIMnic6pusagekl03a_Lkl03a_Skl04a_Zr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~np74lzok" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Lemma nc_bound : ltac2:(zQ "40!h8!j5!j9!je>3csz$1>2nf$1>3cnt$1>2au$1>2mu$1>0@2$0+i0^5>0@2$0@2$3^6@2$2^5^4^3>0@2$0^4^3>0@2$0@2$2^4+kggg0+ugggggg0>0@2$0Z^8>0@2$0Z^8@2$0@2$3+i0@2$2^a^9+ugggggg0").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_CacheDealloc3 ()) [] "##7wh04__x1h14__x2h24__x3h34__x4h44__x5h57__arithh64__ffh78__varmaph85__with92auh:3cnth;3cszh<2muh=2nfp;1p;2p;3p;4p;7p;8p-1R0p10000p4p710p9P!s6%S!s611:!s6'p10022!s4&1002O!s2&8g002kj10Tg003Pj1:!s/$nj21Tg004Jj2?!s/$gj2GTg005Dj15!s/$ij2ITg006Rj2ATg007;j16!s/$Zj2XTg008Fj2WTg0092j1V!s/$Rj3STg00:2j1R!s/$Rj2KTg00;0j1Q!s/$Nj4E!s/$lj1PTg00<Jj1OTg00=5j2B!s/$Xj2<Tg00>;j1N!s/$]j3HTg00?@j3J!s/$cj2MTg00@Ej2T!s/$_j2UTg00AKj3_!s/$ej3^Tg00BDj4]Tg00C6j33!s/$_j3CTg00DHj4\Tg00E3j7Z!s/$Wj8[Tf0R0#0#0p=D%0!s0$#0p=F!s2+!s$'p==g00F;R1/I0p=;f1R2=310p=>f2R3=312=C10p=L%50#5p=@A31209313p=Yf3R4A3132531!sM%2f4R5=31!s=%=C105C1p=9P1P2g00FYP0C\p=4!s4$G@R6g00G_R7P7g00H?R8P0g00H_FZp=7P4P6P7P7P8P3P2P0G[p=8g00I?R6#0R9#0R:#0#DR;#:R</15f5R=1?54'G/131143%0;#F#=#:R;,?4%56R>#5#0#D!s<$=R?!s0$:R@'1g00IdRAf7RB'1RCg00JBRDg00JnRE,I1RF1A1<RGPF%6E#6RE#;RH%6ERE#6RI#6RJ#6RK#6#;RL1>GL3LRLPGPF%;KRK1>GK5LHRKPG%;JRJPFPJPLPJPKPJPJ%:9,A1RM%;IRI,>JPMPJ%;ERE%5?#:,A1R?PJPHPGPIPFPIPLPIPKPIPIPM1>IEP?PI!sD$EPFPEPLPEPKPEPE%0>#5#@!s$+D#=#=!sv$1>HFP?PHPL!s+$KAY?HEC2C2D9D9!s-/!s0/g00KM'X'W%VD3S%RDP1P11K15P3%Q1RDCEP2!s7$=P4PDCECE%P1%O1RD1B1AR?1<19RE'4,7D%N7R7PD1<16R6,4?,7DP7PD%59,<1R91B1;5H11B1@R?!sW$P!sT%:R:/49!s6,>R>AH16ER65J1/4:!s@'B1<R:/4>!s6$AJ1:6/!t3$C8!s$,1MD8P0P3g00L9!xW$LYR8'T1U03=_D8dA^1A2C]b6b7b8X01X11X21X31X4111A2RAf6R8/?;/1@118B1?5=,G8/1B11<B1?8B,G</1@[[[[\A[^01^11^21^31^41P0PBf8f;f9f:P2P3P4P5P=P8O;b5VCUUUUUX<1X91X:1X=1X;1o"). Qed.
(* [comment removed for export] *)
Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma kr_of_flag : ltac2:(zQ "80!j5!l7!n4!nb!rd!s7!sc!t0>7drained$2>3cnt$0>2mc$0>1n$0>2nf$0>3mfa$0>1k$0>4mfa'$0>0@3$1$0^2M2\7drained$2$0^8^5Z>0@3$1$0^2M2\7drained$2$0^9@3$4^5^6^4^4>0@3$1$0^7@2$5^8+2>0M2\7drained$2P^b@3$1$0^a^9@2$6^a^9@2$7@2$3@3$1$0^6Z@2$3@3$1$0^5^7@2$6^b^a@2$3@3$1$0^6@2$5^a+2@2$3@3$1$0^b^a@3$1$0^5@3$4^8^6^7").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_CacheDealloc3 ()) ["HCW"] "##1tp'0h04mfa'h13cnth21kh31nh42mch53mfah62nfh77drainedi00!s1,11bp;3p;1p;2p;4p;6p100M9p4p710R0g00MhR1!s5%p8P0p100NF!s6'g00OLj33Tg002kj1>Tg003Pj1=Tg00PQj2<!s/$nj2:Tg00QJj21!s/$ej24Tg00@Ej28Tg00R?j4;!s/$Zj3@TP1j67Tg00AKj35Tg00S4j3?Tg00F;R1f1R0f0R235p=0g00IdR39512p=6f2R41102'1p=2A5140/12p=9g00L9R5P5P5P1f7R6f4R7P3n0110000020000,00!sE$8R8f5R9f3R:537R;P:!sN4f6R<g00I?#>#=R=,<6'0R>P5p-0f:R5f9R?/08R@1:?8RA!se1%69107<1:5?RB321<?=RC105?RDA369<,07'1599'4[[[[^01^21^51^61^31^41^11P21007100;P1P8%62R;1096f;RE/:5RF321<5=R=,02RG10E5REA3826RH,0932'4X21RIP1A368<%6?A926FRJ'1A38?6,02,1E99?='4X01P1PC10H6=2;F10HH92GE'4X31P1P?%6=A38=6RG/061:253210GG992599=='4X11%6CA36C<RG/0<1:??3210CCRH10??RF10GGR;'1RK'1PHPK181CPFP;181?181GC;C;3@P5P2E7P8P0E7P7P4E7P9P:E7V@V>UUX01X21X51X61X31X41!tF$0100:P1P3PIP1P<A5133RI/1JA513=A3836,0272E!u_$10<<RE/1BR8,1IA513CA363<,0<72DPIP81813PEPB181<P2!tg$?!t[0A!t[<!xr$1!xr$100W7o"). Qed.
Lemma froom_of_flag : ltac2:(zQ "80!j5!n4!hh6!h8!l7!rd!hm3!j9>7drained$1>1n$0>2nf$0>3mfa$0>4mfa'$0>0@3$4$0^1M1\7drained$1$0^5@3$5^3^4^2^2>0@2$3^3$2>0@2$3@1$6@2$7^5^6$2@2$3^4$2").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_CacheDealloc3 ()) ["HCW"] "##+2p'0h04mfa'h13mfah21nh32nfh41bi001bh57drainedi01!s1'p;3p;2p;1p;6g00OLj36Tg00AKj32Tg004Jj21Tg00SNj15Tg002kj14Tg003Pj1:!sJ$gj29Tg00TSj28Tg00Mhj63!sJ$nj27Tf0R0g00U0'7p=0g00L9R1P1g00F;R2P1P2f4R3f2R4f3R5f1R636R7P6n01101000200009220%04R8f5R9,13#5#0R:%05[[[^02^12^32]2P0A2207P2f6R7=693R;%00X02R<g00I?#4#4#:1197'9/83P1!s$$2P0P7f7f8'1#5n!tC$!tF'#0P0P4!t\&!s<+b4%0;eP5P4E3V:V8UX02X12X32X22A2206P2P3P<P6!sJ:!su1W5o"). Qed.

Section CDStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (c p : Z) (d : depot) (lo : Z).

  Let st : ltac2:(zQ "10!hme$0") := ltac2:(zQ "10!koe@1$0?1s").
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let CA := a_cache s.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let pc := get_pc st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let cnt := pc_count pc. Let chunks := pc_chunks pc. Let csz := class_size c. Let mc := max_count c. Let n := mc / 2.
  Let drained : bool := cnt =? mc.
  Let k := if drained then n else 0.
  Let mfa' := if drained then rta_mfa nf n mfa else mfa.
  Let st' := cd_state st c p drained.

  Hypothesis RQ : ltac2:(zQ "30!kp6!j5!kta@5$2?5HCEIL?1s?2XC@3$0$1?1p?2XB?1m").
  Hypothesis CLS : ltac2:(zQ "30!l7!j5!ku3@3$0$1@2$2?2st?1p?1c").
  Hypothesis HC : ltac2:(zQ "20!h8!nb@2$1@2$0+1?1c@2$0?1c+he").
  Hypothesis INIT : ltac2:(zQ "40!n4!kv3!l7!kva@3$2$0@1$3?2st$1").
  Hypothesis AX : ltac2:(zQ "30!nb!lkb!ll7@2$0@2$1?1s?1m@1$2?1m").
  Hypothesis AMX : ltac2:(zQ "10!lm5@3$0?5HCEIL?1s?2mo").
  Hypothesis DEP : ltac2:(zQ "20!jr0!lr0@3$1$0?1d?1m").
  Hypothesis DPL : ltac2:(zQ "10!lv9@3$0?5HCEIL?1s?1d").
  Hypothesis DCOV : ltac2:(zQ "10!mg9@2$0?1d?2mo").
  Hypothesis MI : ltac2:(zQ "20!jr0!ml0@2$1$0?1m").
  Hypothesis LO : ltac2:(zQ "20!mp9!h8@2$1@1$0?5HCEIL?2lo").
  Hypothesis HI : ltac2:(zQ "40!mq2!j9!h8!ms6@2$2@2$1?2lo+ir0@2$3@1$0#k0?2sp").
  Hypothesis SPT : ltac2:(zQ "50!mq2!j9!h8!mt5!ms6@2$2@2$1@2$4@1$0#k0?2sp+h0@2$3+2+if").
  Hypothesis SPA : ltac2:(zQ "50!l7!mq2!j5!mta!ms6@3$0$2@2$3@2$4@1$1#k0?2sp+h0Z").
  Hypothesis ST : ltac2:(zQ "40!mq2!jr0!nhe!ms6@4$2$1?1m?2lo@2$3@1$0#k0?2sp").
  Hypothesis TP : ltac2:(zQ "50!l7!mq2!j5!ni5!ms6@3$0$2@2$4@1$1#k0?2tp$3").
  (* [comment removed for export] *)
  Hypothesis SLOTJ : junk m p csz.
  Hypothesis SLOTP : poisoned m p (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic.
  (* [comment removed for export] *)
  Hypothesis PROOM : ltac2:(zQ "40!nmd!nn7!j9!h8@2$3@2$2@1$1?2st+kqgg0$0").
  Hypothesis OK : ltac2:(zQ "60!jmc!jr0!no1!no8!nof!nt0@5$5$1@1$2?1s@1$3?1s@1$4?1s@2$0?3msF?2mo").
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
                    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz AINST) (wz c) (wz p) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x6b7a0) fc None m (seg_rom asegs).

  (* [comment removed for export] *)
  Definition cd_model : ltac2:(zQ "10!hme>3stX$0P") := ltac2:(zQ "c0!hme!hn7!hne!ho7!hoe!ht7!hua!hv1!hva!nb!l7!ig1\3stX$0>3stA$0>0@2$5^1?2st@2$4$0\4stA'$0@2$4@1$1$2\2ev@1$1$2@2$9@3$a@1$7@2$3$0@1$1$2@3$b^4?1c?1p@2$6@2$3$0@1$1$2@4$8$0@1$1$2^2^1@2$5^2^5").
  Definition cd_gpost : ltac2:(zQ "20!ik8!io7>0$0>0$1P") := ltac2:(zQ "20!iu2!jj2@hc$1?5HCEIL?2ra?2sp?2gp?2tp?2s0?2s1?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?1F?2fc?1s?1d?2lo?1m?2mo?2XC?2XB?2XB$0").

  Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
  Let WQ : WFQ st XC (p :: XB). Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
  Let OKQ : placed_ok s /\ WFQ (a_st s) XC (p :: XB). Proof. exact (conj PL WQ). Qed.
  Let HC' : 1 <= c < kNumClasses. Proof. clear - HC. unfold kNumClasses. tlia. Qed.
  Let HCC : 0 <= c < kNumClasses. Proof. clear - HC. unfold kNumClasses. tlia. Qed.
  Let CV : carved st c p. Proof. rewrite <- CLS. exact (WFQ_xb st _ _ p WQ ltac:(left; reflexivity)). Qed.

  Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SEC & SEC2 & TCX).

  Let BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 7430144 <= CTX /\ CTX + 160 <= aceil
            /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
            /\ 1 <= c <= 30 /\ CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c
            /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
            /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= 536870912 /\ 0 <= cnt <= mc /\ 2 <= mc <= 16 /\ 1 <= n /\ n + n = mc /\ 0 <= au <= mu /\ mu + 262144 <= 3758096384
            /\ 32 <= csz <= 65536 /\ RB s c <= p /\ p + csz <= RB s c + au /\ csz * (nf + cnt) <= au /\ TH mod 16 = 0 /\ sb mod 65536 = 0 /\ p mod 16 = 0 /\ mfa mod 262144 = 0.
  Proof.
    clear AX AMX DEP DPL MI ST SLOTJ SLOTP PROOM OK VISE.
    placed. fold TH CTX sb in T1, T2, T3, X2, X3, S1, S2, S3.
    apply akobj_env in T2; [| unfold kPageSize; clear; tlia]. apply aapp_env in X2; [| clear; tlia].
    pose proof (cd_pure s m _ _ c RQ HC INIT) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11). fold st r pc in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    fold nf mfa au mu fl cnt chunks csz mc in U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11.
    npose (class_size_table_facts c HCC) as (_ & C2 & _ & _ & _ & C6). fold mc in C6. fold csz in C2.
    pose proof (class_slots_count st _ _ c WQ HCC ltac:(clear - U10; fold csz; tlia)) as CNTB. fold r pc csz au fl chunks in CNTB.
    pose proof (ro_numfreed _ _ (WFQ_region st _ _ c WQ HCC)) as NFE. fold r nf fl in NFE. rewrite <- NFE, <- U8 in CNTB.
    ndestruct CV as (_ & _ & V3 & V4 & V5). fold st r au csz in V5. change (region_beg st c) with (RB s c) in V3, V4, V5. fold csz in V4.
    assert (GEO : CA = TH + 208 /\ P = TH + 208 + 80 * c /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384).
    { unfold P, CA, RI, TH, sb, a_cache, a_ri, OT_CACHE, kSpaceSize, RB, FA, a_sb. rewrite free_array_base_eq, region_beg_eq. unfold kFreeArrayOffset. repeat split; reflexivity. }
    npose GEO as (_ & _ & _ & ERB & _).
    assert (NN : 1 <= n /\ n + n = mc) by (unfold n; clear - U11 C6; Z.div_mod_to_equations; tlia).
    assert (P16 : p mod 16 = 0) by (clear - ERB S1 C2 U10 V4; Z.div_mod_to_equations; nia).
    assert (T16 : TH mod 16 = 0) by (clear - T1; unfold kPageSize in T1; Z.div_mod_to_equations; tlia).
    unfold AHI_LO, kSpaceSize, kPageSize, kFreeArraySize, kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize in *.
    clear - LO T2 X2 S1 S2 S3 HC GEO U1 U2 U3 U4 U5 U9 U10 U11 NN V3 V5 CNTB P16 T16.
    repeat match goal with |- _ /\ _ => split end; tlia.
  Qed.


  (* [comment removed for export] *)
  Lemma cd_zones : forall m', munch (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa') m m' ->
    agree_on (fun a => bv_unsigned sp <= a) m m' /\ agree_on (pendz st XB) m m'
    /\ agree_on (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa' ++ [(p, p + csz); (sh p, sh p + csz / 8)])) m m'.
Proof.
ltac2:(KReplay.run1z (kr_t_AG_CacheDealloc3 ()) ["HCW"; "CDStep"] "#+6kp'0p'1h04__x1h14__p1h25__p10h3!s-$1h4!s-$2h5!s-$3h6!s-$4h74__p2h84__p3h94__p4h:4__p5h;4__p6h<4__p7h=4__p8h>4__p9h?!sf$5h@!s-$6hA!s-$7hB4__x2hC1HhD2H0hE4__x3hF4__x4hG2H5hH7__arithhI4__x5hJ4__ffhK8__varmaphL5__withM!s|$8hN4__x6hO3H10hP3H15hQ3H20hR6heq_CAhS7!s/$TXhT5heq_PhU!sA$RIhV!s/$THhW!s/$auhX!sS$cnthY!s0%szhZ!sC$mch[!s9$mfah\!s9%uh]!sy$nh^!s7$nfh_!s/$sbh`4__x7ha4__x8hb2AGhc2MUhd2r0he!u4$9hf4__x9hg2H1hh2H2hi2H3hj2H4hk2H6hl2H7hm2H8hn1qho2q0hp5FROOMhq2KRhr5__p20hs!s-$1ht!s-$2hu3H11hv3H12hw3H13hx3H14hy3H16hz3H17h{3H18h|3H19h}3H21h~3H22i003H23i012H9i022q1i032q2i042q3i052r1i062r2i072r3i086__sat0i09!s0%1i0:!s0%2i0;!s0%3i0<!s0%4i0=5__x10i0>2r4i0?3AG2i0@7!sZ%4i0!yK$23i0B!sP$1i0C1ai0D!w5$ki0E8!wQ&'i0F1ki0G4!s3%H2Hai0I!s\$2i0J1bi0K7drainedi0L3st'i0!yT$24i0N1zi0O2_Hi0P1Ei0Q3ND'i0R2NIi0S!sL$5i0T!s/$6i0U!s~$3i0V1ri0W1Bi0X3CVxi0Y2Hxi0Z2KBi0[2NCi0\2NEi0]2V4i0^1ei0_1li0`1xi0a3BNDi0b2C8i0c2CVi0d2EEi0e3H24i0f3H25i0g3H30i0h2HCi0i3HC'i0j3HCCi0k2Hqi0l1Pi0m2RIi0n!tq$7i0o!s/$8i0p!vl%19i0q!vw&0i0r!wJ%5i0s!uB$4i0t!s/$5i0u2aui0v6chunksi0w3cnti0x3cszi0y2fli0z2mci0{3mfai0|2mui0}1ni0~2nfi102pci116ACEILBi122GTi133H26i143H27i153H28i163H29i173H31i183H32i193H33i1:2Hui1;3KR'i1<2LEi1=2NDi1>2X8i1?2Y1i1@2Y2i1A2Y3i1B3_H0i1C3_H1i1D!ue&1i1E!s1%34i1F!up%6i1G2b0i1H1ci1I2m'i1J5nd_i1i1K2q4i1L2q5i1M2r5i1N2r6i1O1ui1P1yi1Q2zhp%0p%1p%2p%3p%4p&0p&1p&2p;1p;2p;;p;3p;4p;:p;6p;9p;Cp;Hp;8p;Np;5p;7g002kj16Tg01\Sk119Tg020gk11FTg021Jk11[!s0$lk22MTg01L`j2KTg013=k20TTg022Vl;ITg023_j3dTg024bk41bTg00ank11WTg003nj21!s/$Pj1CTg005Dj1>Tg004Jj24Tg00QJS00j22!s;$gj2:Tg012;k20pTg014?j2DTg0263k22L!s0$Uk21!tT$72S01k2!tk$0OLk307!s=$Uk4!uX$28ek10xj2eTg029jk30HTg00Pnj!sq$0RZk31NTg00o;j!s/%AKj3ATg00@Ek20k!sU$Qj2?Tg01ENk10ATg01FZj1UTg01B0k11!v;$=Fk11JTg01<2k10jTg01:[k11ITg019Lk11GTg01WZk12<Tg01X^k128Tg00`jk125Tg00gEk11zTg00e;k11yTg01Yek21tTg01[bk20qTg0092k110Tg00:2S02k11BTg00;0k11j!s0$lk11hTg00<Jk11fTg00=Xk21ETg00>;k11aTg00?ck21]!ug$_k21\!uz$ek31ZTg00BDk41YTg00S4k31X!sl$5k21;Tg02;2m;1VTg00TSk2!v/%R=j2n!s/$^j2sTg01SEj2m!s/$lj2qTg01TRj2rTg007;j!tJ$1UYk10zTg01V7k20g!yB$ik21STg008Fk20!vQ$bdk30nTg02<Bk22J!s0$bk10VTg02=dk32HTg02>ok42Gk31OTg00Mhm:0vm91sk61@Tg02?Jk22!{W$?lS03k32ETg02@Pk22Dk32=Tg02A[k12CTg02B]k12BTg02Chk12!y6$R?k411Tg010Yk21!tE$E9k11:!wf$Rk30!{;$_ek62!vM$F7k2!{F$2G;k12!}0$HJk42!zt$ISk32!zt$JcS04k20!vA$2Ok60|mC1rTg02K?k2!|F$2K^k61DTg00]8j!}^%8?k20hTg01@gk2!}#$1>Wk11xTg01C;k11wTg00^Hk30}Tg02L;mH1qTg02MLk81!}$$KSk20`Tg01M=k11oTg01NLk21!w=$N`k20iTg02O@k31!xF$ZVk21l!z^$>k31k!sD$dk21u!x?$Xk41v!{`$9k3!~\$2Pok21!|W$]1k31!sv$QXk41g!s:$Tk81|Tg02R2mN1}Tg01^Yk220Tg02SFk621Tg02TKk41!~9$UPk5!#3I$QeS05k223!|%$Rk21d!{t$Nk40@Tg00DHj4!~4$E3j7fTg01aWk617!s0$3k61cTg00Z_j7!{?$EWk80J!|A$]k30!zM$?@k30!}F$U8k21`Tg006Rk21MTg00C6k315!zk$;k31=!s:$_j3!wA$7Zk21<Tg02VTk41PTg02W4k31Q!s0$Qk31_!yK$Nk31^Tf2R0$0xf1R1f0R240Hp=v%62#6#6#6p>181401/12p=F!s=$p=p%>2!sA$2%>2#>p>0Q!sW+!s$&Cp>0E%62#Cp>2>!sM$#>#>p=i!sP36p=y!s:'Cp>0>g00F;R3?A12p=514129A30p>0Xf3R41:12,405A3p>04g00IdR5!tl$;1101/22p=J1112,20p>0\1:!u3&tAA325p=8!s-$,21p>0Z12!sO%=Sf4R6!s4&,24'2p=3f6R7f5R8!s=,,26'2'2p>0=AA3!t<&ZAA3!t='m12010232p=Y20k32p=PP7P8P6P4P0P1P2H11H11p>0F21d32p=_P3!s@&0@p=\21E32p==P0g00G@R9g00G_R:P:g00H?R;P3P1g01cGR<P2Ckg00H_R=Ffp=RP1P9P:P:P;P2J17p>0P!s91cp=9P0!s8+!sp$0FYR>P2CkP!sk$7P6!sF+4!s0+0P1FVP2FVp=Q!sG0!ss,1P2FVFVp=0!t04[CR?!t0+>0_P7!sG+!v8%!t5-P2L0JL0Jp>0512!w%%>0^21;32p=B!t?3p={P8!s9+!th0FV!st&p=E!sp&!x1%p>0OB0S312p=@B0t!s/$X1101,24!xA$u1412,:0p>0o!yW$429A34p=T1L52p=`11501L12'2p=g1L25p>0M1L011125'2p=l1L!yp&<21`52p>0Lg01oe00k2p>0Y21M32p>0021S32p=aB15!tW$GB1=!s/$xAw3129w30p=OB15301=w32p=W21M31>15!sg$yB1=!sA'>0f!s[$g00KMR@+1<p>0eg00JBRA@0212p>0dP3P3!zO%H0@!z8+H!s;&!zL,H0@p>0W!sU$3!{+%H0@!s^2>0KB0t301>0S32p>1R!wL-3P4P<!sE-!xq+IP3P1P!z5$p>03!z283P0P>P1!sZ%!xZ$>0?f7RB!sH+7!xi0!y]/!y:,!sb&!zY%}!{C:=Ff!yB'>06!yg8!uA$P0!t\&!yo'c!{10!tZ/0L0J!sM+j!y[&p>0w1K01=A!ws$G1164!#3d%'2p>0U!#4q%!zf+c!wA$8P6H1P!s1$0P1H1P>02426027p>0Ng02X:RC@1Q12p>2I115!|D&;B1QC40$0x@0H!xj$:!t/,p>0b114!zq$'2p=|!yP$p=^B1_3!sS$]21<1@>02A2p>01!|8%:0S30p>0l1140/2!t8&uAA3!uA/=o!|P$L0p=zAA315!sM%8!t?$!|F$#Np>0914!v6'D!th&#Np>2@!x;:2FVJ17p>1L!|&+9w349w36p>0R!v>$<!~9%!yo$a!y}$<!y}&s!sF$?!sF-BP!yc1!y49!#6A,P=Ff!tR$!yA%C!sNAp>13!t00!yA,=Ff!#6F@FVp>2?P3B0S30!|9+1!#;F&p=b!yS$L01'2#N/22p=~B1^!x$%[1M12#Up=[!w7,p>0{1D12=A35p=h!v8$?!s|&?1:!#<T'~!|WAp>1{%N!xe%1~g00I?S06#6R=#6S07#6S08#6S09#6S0:#6R9$19R?$1FQ08$19$1F$1[S0;[p,2loR>p,2sp-2M?R?p,1PR<p,2CAR@p,3cntRCp,1kS0<'KS0=p,2RIRDp,1sREp,1cRF+0TRGp,2THRHp,2nfRIp,3mfaRJp,4mfa'RKM;IS0>p,1mRL;d2Q0>PL!#<z$bQ0>?vL1p,3BNDS0?p,5HCEILS0@$1WRM/1>S0A%69RN#6$18RO#CRP/1HS0BAFHPMS0CQ06#>RQ#>S0D#6S0E#pRR$12$0Q#p$18$0Ep,3CTXRS'1RT%>=S0F#6S0G#6S0H#pS0I$2>=FSMRU%6OS0J$0QS0K#i#iS0L$0Q#i#y$0ES0Mp,2sbRO'1RVQ0J#6#pRW#pRX#6#pS0N#6S0O#pS0P#6S0Q$18RY!sK$Z#p$0>S0R,4OS0S?FPMS0TQ06#CR[/1FS0UQ0D#>S0V#6S0W#CS0X,1FS0Y'2S0Z%6QS0[#>S0\#6S0]!ss$^,4HS0_,5@S0`Q0_Q0I#CS0a/:FR\60X<S0bQ0S%CNS0c/:FRN60XDS0d20pEFS0ePOPF%CZS0fH04S0gQ0e%6R#p#y!uf$RR60XGS0h%;IS0iQ07#CRZ/:IS0j/1JS0k%CYRY,1JS0l%;CS0mp,2mcR],1CS0n'2S0o%C=R^Q09#CR_,1]S0p7J]S0qp,1nR`,1[S0r14``/5]S0sp,2auRa#;S0tp,2muRb80\aS0u%CXRX=FbRS0vQ0:#CRcp,3cszS0wQ0w%CWRW'1S0x3JS0yQ0ep,1pRd'1S0zQ0w,4dS0{Q0e/4a'1S0|Q0w14ICS0};taS0~1DH_S10#8S111DOWS12#8S131Dd_S14#8S151DJXS16+0Z3SS173SS18'2S19'2S1:'2S1;D3S1<'2S1=3SS1>K0=D3D322LC]S1?15C]S1@21TC]S1A+2KS1BQ1Ag00L9ReQ01Q1@P1PePeP3P2P`P5n0110K00020000S1CP3!sC$1B07I`JS1DPJ!sJ3EP3p,2stRfPFPdP0H16S1Fg02Y;S1GP>P?P<P@1KC0PDPGPHPIPJP1M;IS1Hf;Rg7dLRh!sM-4S1I!sP-0M;I$0xS1Jf<Ri80HLRj!tb$B!u#5Rk#8!sB%Q!tx5Rl1!v6$K7ZJQ1@B07IkJ80ml9Zk`3Y]b]cc0Lc0Gc0Fc0KP1Q1@g00LYS1LPeQ1CP3Q1EP3Q1FQ1G%8`S1MQ1D/5JS1NQ1K3S15``RkQ1@Q1DQ1D'5S1O'2Rl'2PkPl%P`!sA$OP7Q1D#PK0F41NXbjXch!tG/Y0PP2O1Q1@#NS1Pg02ZFS1Q!tQ5AA355S1R15JJS1SQ1K!t;%AA35`!uX&5JS1T,5JS1U3SQ1RPl20k35Q!sU$%PJ1?]^S1V#PQ1V,5`S1WeS1XQ1W&0AFRl#P15]lS1YeS1ZQ1Y%UFS1[#PQ0wQ1['5S1\eS1]Q1\p,2pc$1KRk#P15CkS1^eS1_Q1^p,1rRk$1JRm#P15bmS1`eS1aQ1`&0jk!s<%amS1beS1cQ1b&1I!s<&JmS1deS1eQ1d&1GkS1f#PQ1f,5IS1geS1hQ1g&2<ES1i/4NRN#P15DNS1jeS1kQ1j14@\R\#P15<\S1leS1mQ1l&28E!s<%@\S1neS1oQ1n&25ES1p#PQ1p,5OS1qeS1rQ1q&1z!sU&S\S1seS1tQ1s&1y!s<&H\S1ueS1vQ1u21t]^S1w%;]%;^S1xQ1V#;[[S1y20qd_S1z%;d%;_R\Q14#;S1{[[S1|20qOWS1}%;O%;WQ12#;S1~[[S2020qJXS21%;J%;XQ16#;S22[[S2320qH_S24%;HQ10#;S25\\[S26p-0R\&10ARS&1BARA%_0S27&1j3RN7\1S28&1h3Rk&1f3RmQ06-1E3Rn%==R=5Rm-0Pm&1a:R:PmPm19m6S29!s/$8S2:!s/$7S2;!s/$BS2<Pmf8Ro,9mS2=Pmf9Rp!s2$>Pmf:Rq!s2$?!sS$gS2@!s/$iS2APmf=Rr!sD$BPmf>Rs!s2$CPmf?Rt!s2$DPmf@Ru!s2$EPmfARv!s2$FPmfBRw!s2$GPmfCRx!s2$HPmPmfDRy!s4$IA7mn=S2JfERz!s8$KDQD0!s$1P:B0_mn=K0521]m;R;P2P0Q1L-0ke21\20Q1L5AedB1Z351H1YR{bJbKbLX03XB3X1\X7\X8\X9\X:\X;\X<\X=\X>\X2\X3\X4\X5\X6\X?\X@\XA\WM1521g01oHR|[P4P6P8P7PBPoPpPqPgPiPrPsPtPuPvPw1110S2L>0^xyD3!s$%1L04[[^03^B3^1\^7\^8\^9\^:\^;\^<\^=\^>\^2\^3\^4\^5\^6\^?\^@\^A\^M\P2Q1<Q0mQ0lQ0kQ0iQ0hQ0gQ0dQ0bQ0`Q0ZQ0TPVPUPTQ0CQ0BQ0AP]PCfJS2MfNS2NOFbHc08c09c0:c0;c0<bVbSb_bRbTbUb^b[bWb\bXbYbZb]K0F41X!#5G6\P2O1n10210J10V00021010^1110}P6P4O2c0JbdPeP3Q1A!#8G5h!#8G$Q1A!#8H6j1LClS2O7ZJ1?l^S2P15ClS2QB07IhJ80mj5Zh3YeQ0<#8S2R15KJS2SQ2O'2S2TQ0<Q2PQ2QQ0<>07IJ,5KS2U'23Z3YS2VeQ2VQ0wPIPCPaPbQ1XQ1WQ1ZQ1YQ1]Q1\Q1_Q1^Q1aQ1`Q1cQ1bQ1eQ1dQ1hQ1gQ1kQ1jQ1mQ1lQ1oQ1nQ1rQ1qQ1tQ1sQ1vQ1uQ1wQ1yQ1zQ1|Q1}Q20Q21Q23Q24Q26PSPA%_1S2WPk!}h&4S2XPmQ29PmQ2:PmQ2;PmQ2<PmQ2=PmQ2>PmQ2?PmQ2@PmQ2APmQ2BPmQ2CPmQ2DPmQ2EPmQ2FPmQ2GPmQ2HPmQ2IPmQ2KPmfFRh!|a$YPmfGRj!s2$ZPmfHRl!s2$[Pm%BcS2\=7mnR}fIR~!s>$]5{mQ2M!s2$^!}C3!}I'P}EEP;P!|w-!|tUXM\Xe\Xr\Xs\Xt\Z0A\Z0M\P1P0!}%CPxPyPzPh11c2PjPlI0O!}0'D311c1!}1$!}-X^e\^r\^s\^t\`0A\`0!}B%9Q0xQ0vQ0uQ0sQ0rQ0qQ0o!}TPQ0wPzOJ!}KP!zj~!zj@6S19?\0NS2_%_4S2`7\1!zz%!zgsQ2YPmQ2ZPmQ2[PmQ2]PmQ2^PmfKS2a!zE$bPmfLS2c!s3$dPmfMS2e!s3$fPmQ2N!s1$g%=QRQ,@=,XnQ07#=R}57mS2hfOS2i!sI$j5{m!{89D0P:Q2h!{;3B3XE3XF!{DnZ0S\Z0T\!{FIPjPlP~Q2MQ2aQ2c1410=t24Q2e!#Jj%!{X&404=t16!#9g&E3^F!{en`0S\`0T!{m$7Q0|Q0zQ0y!{sbPaPCPI!{y%O!{y~!{ykQ28!{f'!#7Yz!{p0Q2J5{mQ2]!zk;J!zk6!zed!#6yLP2P1PjCu!zD,Q2L!#A$_!z9/P2Q1;Q0t!yu]bPaPzOI!yp~!ypmW!yp'!#>P~!yu+%BXS0t,@n%BRS1;57mRaQ2[!#5r9P:Pa!#>&s!#=zLAF2XRPh!#5E,AF1XR!#=vhP2Q1:!#4s_bPzOH!yz~!yz~!yzX21;35Rb=7mnS0qQ2E!yL2P:Q0q!yE\!y,=%;2S1:Ps!xv&%;1S!#3t%!xsLP2Q1>!xCHIPzO@!xC~!xC~!#3?aQ2G!sv$0qQ2HQ2IDQS1>!~w4!xSa!~r/!~fCQ1:@0^vwS17!#9\2!#S[^n!~CQCPzOD!x~PN;1VQ0}=tcRQ1?Q1BQ1AP!#fP,!#aa2Q1H?dLrS1HQ1J@0HLsS1J%86Q2O9Z4J!#R;$B07I6JS0180m45Z63YS1APeP3PoPeP3B0oZI`S1B01UJS1?PJQ1B/4X/K[Ra/?XS0}/:XS2hn010!s#$20000!#T;2/1Y]q!#eC7Q!#e>6Q!u%$Q1AQ1?Pe!#hz'JQ!t63/1YP2!|6~!|6~!|65%BYS2X97mnS1LQ2G!|171L!|1bS1L!|-A112YP!#B_'111YS2k!|'WS2lP2Q1=!{zNJfRS2mOB!{}P1naXS2n%8XS2o#NS2pPaPXQ0}1DaXS2qCT[S2r1saXS2s%`XS2tQ2qQ2q;gX[S2u1maXS2v&0MXS2w!sA%5lX[S2x1qaXS2yQ2oQ0}#8[S2z1raXS2{Q2oQ2q/5a[S2|Q0}P3Q2qP31nH_S2}%8_S2~#NS30PHP_1?H_S31Q10CT[S321sH_S33%`_RaQ25Q10;<_[S251mH_S34&0M_S35Q10Q105l_[S361qH_S37Q2~Q31#8[S381rH_S39Q2~Q10/5H[S3:Q31P3Q10P31nOWS3;%8WS3<#NPOPW1?OWS3=Q12!tV$>1sOWS3?%`WS3@Q1~Q12;<W[S1~1mOWS3A&0MWQ12Q125lW[S3B1qOWS3CQ3<Q3=!tT$D1rOWS3EQ3<Q12/5O[S3FQ3=P3Q12P31nd_S3GQ30PdP_1?d_S3HQ14!tO$01sd_S3IQ1{Q14;<_\aS1{1md_S3JQ35Q14Q14!uw%51qd_S3K!uw$H!tI$L1rd_S3M!uw$4/5d[S3NQ3HP3Q14P31nJXS3OQ2pPJPX1?JXS3PQ16!x~$p1sJXS3QQ2tQ22Q16;<X[S221mJXS3RQ2wQ16Q16!xw%w1qJXS3SQ2oQ3P!tK$T1rJXS3UQ2oQ16/5J[S3VQ3PP3Q16P3P8&0LX$0YQ2teS2tO1S3WQ1:?<2XS3XPr&0L_$0YPaeS3YO1S3Z%;oS3[?<o_S3\Pz&0LW$0YQ3@eS3@O1S3]%;uS3^?<uWS3_Q2eQ!s`%`%;lS3a?<l_S3bfUS3cQ!t@$2tfPS3d#;S3eQ3d;<XS3f!#6+|&00ZS3gg00JnS3h#]S3i#]S3j#]S3k#]S3l#]S3m#]S3n#]S3o#]S3p#]Ra#]S3q#aS3rQ3g%aaS3s'GS3tQ3p#aS3pQ06$0z-0g3S3uQ3o#aS3o'xS3v3O3WQ3i#aRa%C9S3i00yaQ0O#C$00Q3h-1S3S3h&0z9!se$0OQ3q#]R9!tA+wQ0O%a9S3xQ0:!t4&Q3pQ3oQ08#CR9$00S3yQ3n#aS3n'GQ3yQ3m#aS3m&00cS3zQ3k#aS3k'G3W3O40f!s%%3W+0e+0<+0<00dSPA%_8S0OPpPNPpPNDH!s0%%_BS3{Pp%_pS3|!s:$4PNDHDHP1%_7S3}!sN%Q27!sa'P6%_oS3~I0WK0KDH!#:$%0\#=S40Q07#>S41#>S42#6#=S43P:!sH%8#>S44#=S45Q0V#>S4!sF$7!sF']#=S0]97mbQ2@!s;'t=Rmb-0PmS48P:Pm%BZS49Q40Q45'@Q0t41R%B[S4:60n3Q0tPnQ0]I0I!sg'V#=S0VQ09#=S4;!s<&2\Q40Q0V'@'XQ1;+0!ts'!#`|h!to$'XQ0E#=S4<57m!t'$4<Q2X+03P!#aF$PmPm%B^S4=Q4;Q2bI0?S4>PmQ2dPmQ45!uX%4;5RmQ2fD0D0G}!#F52t,XnQ2X57mEEI06EcFjEEEcEc!#a-9I3XN3X`3Xa3Xf!#RW\151o157oQ3[/2gQ2oP|[S2o148p>0wZXB0wX6q80G[[15Bo147o=tcR!#aC?Q2e1:ZBPoPoPYQ2N11^qS4?Q2i'2Q3d14ggS4@/5qfQS4A3SI0UI0c!#SJ%tBXY[!s#%!#aj/I3^N3^`3^a3^f!#Sh\P2Q0uQ0vQ0yQ0zQ0|Q0~fZS4B#8S4CfSS4D#8S4EQ2c#8S4F00ZzD3D3Q0rQ0pQ0o!#?mIfaS4G/LXQ1fQ1VQ4GP`P]PCPJPIfbS4HPoPtPufgS4IfpS4JftS4KfvOSbHc0@!#@9>bDbGbObPbQc0>c04c00b~b}bQb|c07c03b{bzbybPbxc06c02bwbvbubOc01c05bobmblbkbGbjbdbnbibhbgbDbCn0110J00020101c0JWqWbWc!$,87PQ!$,-6!#HA,!#Gt~!#Gt6Q1LQ!#DZUQ4A!#DXQ!v37!#y|210211!#y|'7P8P4O3c0Jbdg00U0S1P,1KS1HeQ1HQ0>22J33S1HPdQ0{Q1H&0V!$7l${Q0w/?9'4Q1H$10S1JK0NS1A+2IS1=/e2P7P1Q0>/e1S2lQ1A/e1S1LQ1=/e!s>%0!s;$0'2[Q2lQ1L'2!sC$0[Q0>Q1A<2H1P2H2G41OO2Y0HZ0C3Q1=$0xS0>@0HL7S1LeQ1LP4Q2VQ05Q2RQ2!$2P$S2V'2S1LQ0</5`S1FQ1@Q2U'2S!s'$1E11KYS1CQ0<Q0</1CS1Q+0;S4L11JKS4MQ1C'2S4N'2S4O]pS4PP2Q1LQ00!t4$VQ!s7$2RP3P5!$7M,2!$7J,KM;I?dLsS4Q!sH-1!sH3vLtS4R%80Q2T!#Qi+0J80mK5Z03YS4S!sf'Q!$8S/KM;IQ1APLPvH0:S1IQ2VQ1C%;7P7PCQ4NCu]pS4T[_0?!#QT$Z0F3!tZ-5S4U!sv2S4V?dLrQ4V?vLsQ1R!td%9A35S4WQ2QQ1T,5K3S3YQ4V!tL%uH0:!wH$0!wE%Q1C1155S4VQ0m'2S4XQ4N'2]pP2Q2SP3PJ!uF+!tN02!v,%h!sD91!vm%j!tb$O9Z0JS4YQ!tb,03S3Y!sa94!vG+~H0:Q1K118YS1TQ4XPJP7117YS4XH0b]p!vJ&c]bZ0G3!su9J!vF$U?vLzQ4U?dLhQ1RQ1!$&7$!t`'U!vA%U!tF%l!tF%Q0l!#4,~!#q>~!#@22Q2X97m=S2;Q!#^'7PmPmA7mbbQ0qPmPmP=P=Q2;I0?DQ!#q:g!#^BA2kQ!#^=,4VQ2LP0!s$$YC|40^!#q'\!#^M+!#7rLPCf\S0n!#^OQWpY0OY0?WqWcWbPKP2!uc$8P6N:0vWCP1P2O2n20!#[z&12!s/&WC!s]%bWcQ0<P2PiPgPpP7!s^E!#<2$EQ00Q1FQ2U!#5?$1FP3P`Q4QQ4RQ4SQ1IQ1@Q0180mKQ!#3h=`S4Q!#3h3R!#3h$R!#3h$M!#3h$,5`S!$3T$1D,5KS4S!|O%R!#3j,1@Q4S'2!tj$@!tU$C11`C-0;`S4R!#3k+!sC$P3Q1D!}w,Q!#3o4j!sD9!#3o%lQ1MQ4YQ!tc,!#3h1Q!#3h6Q2MH0:116YQ4RPJP8Q1TH0b]p!#3^9!sk-Q1D!v=$Q?vLhQ4Q!#5C$MQ1N!#3_$!tW&O!v6%Q!#5#-B02FJQ1B/1JS1AQ1B,LJS1BQ1?42EQ1?PeQ0!$8U$B!$L$$!#bI8!u%%eP3P0!sG6S03Q03/1Y!uF$P1Q1A!#4~~!#B,<3q!#R:&03Q3j#aS3j'^S1?&00^S4QQ03Q3nQ3uQ3l#aS3l'xS1M'^3WQ3h,GaS2PQ4Q/GaQ3zQ3h'GS2Q3O+0]+0]S1O!vz$?Q3uQ03'x!t2$uQ3w'xQ3l/^aS2O3O!wS%7OaS2Q!s_%'G'^001SPAQ3~P8PNPi%_qS2P?\iNDHP0Q19P1PNP7%_gS1NPiQ3{P4Q3|Pi%_iS4YPiPNDH!#RM-42#=S42Q0\#>#=S0\!#6U$PnQ0[#6S1C!s=$2T!s=&=Q!#Q1+C!#O^$PS1IQ0[#=S0[!#7l40M#BS4TQ08#=S0857!sa$G!ss$mQ4:Q41#=S01Q2HI0?!#QG440Q08Q01Q0f#BS4P40l5Rm!#Q`42X97mQS2U!#QJ%Q4>!t-$=7mnS4>Pm1@nnS1L!#Q=$!#QR&2f!#SL'257mQ2g!te%0Q0H!#U]$2jI0?!$F:4D0D0I0?P:!#qJ%J5{mS2JPmA7mQQQ2UD0!#Qu$!#QwIZ0=3Z0B3Z0I!#R'Y15og151g154pPtPPP7!#Q[$Q0M/1BPx11[oS2U/2!#Qi&pPBPoQ0fH04!#Qu&1TQ2aQ4?Q2c'21444PqQ2eQ2NPcPgQ2iQ3d9JpiH0uDo9J[4!#;B&H0b%;6S1TP6P8Q4X9J77Cu!#QzA`0=3`0B3`0I!#s;]8!$=T,!#QV$!#;x'!#;u'YQ0T!#;s'AQ1[Q1VPdQ0wP]Q0ePFPOPHPJPCP`PvPxQ2Nf`S0YOR!#<7R1<!#:x$BQ2h/1YQ2nQ2rQ2sQ2uQ2vQ2xQ2yQ2zQ2{Q!#ig-Q2}Q32Q33Q25Q34Q36Q37Q38Q39Q!#h\-Q3;Q3>Q3?Q1~Q3AQ3BQ3CQ3DQ3EQ!#gV-Q3GQ30Q!#g:$!#g'$3KQ3LQ3MQ!#f[-Q3OQ2pQ3QQ22Q!#f-$3SQ3TQ3UQ!#e^-Q3WQ3XQ3ZQ3\Q3]Q3_Q3`Q3bQ2tQ!#d:~Q!#5~'03Q3vQ!#5k$!#5b,Q3g!#7O,1O!s6$wQ3uQ3x'xS4QQ3oQ3u/xaS1?3O3W3W!sF$j/^aS2Q!sg$/Ga&00XQ3hQ07!#dN&07!s~$#]#aQ07Q1O!s]$x'^!#br7+01PAQ0OPrPNP6Q3{?\rNDHP0PNPrQ3|Pr%_rS07!sF$rQ2P!#bu$Q4YP7!sI%~DH!sC$4PN!sK&1NI0W!sN$!#7M%;Q!#b^'40Q09#>#=!#7Q'!#bY'!#b9$PQQ0tQ0W#=S0WQ2T!#a{+2DQ0]Q0t60_m!sY0Q49Q4;/@n'XS4;Q0t'@Q!#bh+}!#bh+Q0t,X}S0t!#`;$S4:!se%;:0_mQ!#8t+5!t@'!$DPWQ2b!#7I-Q2gPmQ2jPmQ3d,9mS4;!u2%=Q45!tT$8Q4A!s?$7!#8I&1LQ45!#89%m,9mS1LPmQ4D!sL$>!#dk+57mfTS09!s>$3PmQ3c,9mS3qPmfVS2O!s3$vPmfWS3f,9mS2tPmfXS2q,9mPmfYS0}!s0$Q4B,9mQ2T=Rmb!#8r%Q!s+-!#L%1Q2J!vl$97mQQ4:!#8~$K05FjEEFj!#91YZ0U!$FQuZ0n\Z0o\156i15Bi150iQ2oP7PXPrPgCT[A<viXQ2o14q7!#df'ps80G[[AtpXYB0oZgB,Lp15pr!#d^4Q2N!#9U$Q4AQ2mQ4DQ09Q3cQ2OQ3fQ2q9J^sP[Pp14ppPsQ0}Q4BPcPtf[S2oQ0nf]S4:f^S0tf_S2JQ0YQ4G%8uK0=H0uDo!#e7'D3%;qS2T!#O1$1:rXS2|Q2|PYC|!#:Q$!#eSC!#:W-`0U!$H^u`0n\`0o\P2Q4FQ4EQ4CQ0~!$Ho&!#;61!$Q^N4G#;Q1f!#;I%hQ4GPzQ0wP]PIQ4!#;J&oPrPtQ2aPuQ4IfhfiS4IfrS0wp+01EOc!#ey~!#ey@WpY12P2O1n2002!#f+$!#bL$000!s'$c1Gc0JQ1D/1YRIQ4RPJQ1DPIH0b]pe!#RF0BPoP7P8!#Qf$Y0P!#RIz!s@-!tx0;P1O1Q4O11?2S4OZ0C3@0HLoS1Ep,2XBS1F-2Df!s:&@Q!#bp$oS0>'2Q4OPoP1Q46!$zW$iRI#6#i#i!$w{%S46PM%>IS4S!s<-,1MS4R1DMPS1BQ0@$2CRIAzIMP5JMS1[+08H0uRIQ0K#!t#%$12#>!${_%&0VMS0KQ0KQ0L#6!s>+C|S0L!st$!sz%AH11Q0L,2IRIePIP>P0P0P?H09P<P0P014<ZS0KH09S1fQ0=,:ZRI:0D<_S0=P0P0Q0H#CS0H>0D<IS0xH09S4CQ0I#>RI#6$0>,4@S0IP0P0%>I$0>S4E,4@S4FH09S2|PD!t6%D9S2{!s9$z14D_S2y!s>&cS2!s|$2vQ0a,4DS2u!tG%F#>S2s$0>S2r!s>$n!sM$hQ0j,4GS0j!sg%GKS1A!u7$8Q4S!w8&S14GJS4X/?9S2R'4RI1KKJS2V!s7$S9z0I82@0S1KQ0G$0QS1<#>$12!uF$HS4V!tQ$1C!wA%p$0>S17,4HS2k!tS$;g020KS1>'2S2:'2S28'2S4U'2S1R'2S4W'2S1!s5$S'2S4Z'21nMPS4[%8PRI#NPMPP1?MPS4\Q1BCT[S4]1sMPS4^%`PS4_Q1BQ1B;gP[S4`1mMPS4a&0MP!s>%5lP[S4b1qMPS4cQ4\#8\IS4d1rMPS4eQ1B/5M\IS4fQ4\P3Q1B!#FZ~!#FZ~3bQ3c&0LP$0YQ4_eO1S4_Q!$+/%PS3ePeP3p,!%`c&S4g!$is6I#P15KIS1DeS4hQ1DPeP3Q4g!$jd5`#P!#m]%4geS4iQ4g!#G~|!$<$%Q277\0!#E6$203Q!#D}%Q29B0_m=QH1LI06!#dt51112A<410P|!$op,P2flR`,1>P?P`fkS29O4!#8xCc0Dc0E!#8~{Q1fQ4ZQ4[Q4]Q4^Q4`Q4aQ4bQ4cQ4dQ4eQ!zj~!zj~!zj2!zZ%!yy$Q!yR~wQ1y!$1K%3nQ3mQ0a$00S4ZQ3lQ3kQ3h,^aS1f'^S273WI0R!#]C%19P0Q3~?\7NP1Q3|?\BNS4jP8!$0t,!$0K%G#=S0GQ0a#BS4kQ01'X60anP:PmA7m}=S4l!ze&0F#=RI=7mQS4m!#mh&0[Q1I'@=7mIS4n!#my;Q01Q0X#BS4o57mS4p5{m!tN&Q0[Q0^#BS4q'@S4r+0s!#L/LPmQ48Q2]Q2^!#Ik+!$-j&P:PmQ1<#6$0>S1<#BS4s,@Q=7m}S4t!}3'bPmQ49:0B=nL0CK05!}:7!$/%iP2PBQ0aP7H0411601176S4uPg14BPP7!$ZT,oQ0XPpQ0^,4B!$-x2Q4?P~Q2M!$qa$oCuD3I0cQ1<=F87Q2e146Z7<8P|!$-SuP211<`Q0rQ0s!$-W4Q0nQ3cQ2N%8j+08!s%%D3D3S0n!#Gd?U!#Ga,BP]P@PFPHPMP?P>P`P<P7Q29Q0wp,2HIS4?ON!#5?~!#5?G4CQ1S!#5?~!#5?~!#5?~!#5?\xQ3rQ3t!#5H%4ZQ!$?^$mQ3gQ3l'G!s-$jQ1f3WI0R!#5D+3~P6Q2PP0Q1NPgPNP7PNDHP1Q0OQ4j7\4K0K!#5E%1C#=S1CQ4kQ2s#=S2s!#5E+Q0[!~y%k!~y%!#{1$QQ2BQ2CD!#Y`%Q0D#=S4j=7mIS1f!#58&08Q1I'@S4ZQ4j!#k9%!#Y~4PmQ2IQ2sQ!#5\$3t!tb&Q08Q4q40a!#ZDG!$=='1!$@t$1-03=H13!#Z?'157m!u[$1%B_S4q57mQ2f!#5v&L2!#j|'!ul$4s,@IQ0[57mS41!u\&2gPmQ0H#B,@nQ49B0n3=Q'X60B}L0CEE!#5}M!#X|&!$]mY2PpQ0aPoH04Q4uQ1T@0^rsPpPBPuAFqPpS1T!#5w,gQ0XPiQ0^,4q!$=~6@0\6r11^r11r_Q2N!#6B/UQ1<=FopQ4AQ0H1K7B,:Z60D87<o!#6L%!#WMF!#jz[0=/1`Q0n!%3r<!#5~/Q4NQ1Q!#6+2Q0<PC!#61%fmS1QQ0wQ4?!#j{$!#61~!#61C2|Q1U!#61~!#61~!#61~!#61\nQ3mQ3lQ27'^S1U'^S2|!#zQ'19Q3}7\0S4NP1Q3{PBPNP8PNDHP4PNI0WPkPmQ!#Cf'!#C[$>PmQ!#CO$!$2T9PmQ4r-0snP!$KkK!#C+%ZQ2[!#C++S4r!#C//!#Bp+]PmQ4E#B!#Br,!#3pB!#3bT1141S4n1184S0mPo147PP8!$38+Q0^:0X17!$vD211^BPhPj!%5>'!#BY&68S0^Q2MQ4E,447<6!#38$!#368!$3gW0I!~}'!#B$=Z!#B$1!~v+P@!#Az$Q4?OK!~j~!~jJzQ4W!~j~!~j~!~j~!~j`!#P3'cQ3l+0yQ27!#AZ%S27PAQ3}P6PNP0P!~l$~!~l'P4PNK0KK0KS4!~p8!~f=08Q0R#BS2z'@RCQ1I<14I!#uM&4p!~z/PmQ0c#BQ01'X:0anC!#OEB!#3:%[Q2]!#3:&G}DQ!#39$!$Z0%!#3:,^Pm%B9S4p!#3;Ma!#3>VQ4nQ0m!#3--R,47RC/4PP8PsPBQ0XP1Q0c=bC!#Nx0^PoPjPlH0uD3Do9StuCuI0cD3RCQ0^Q2a1449!#3>Aa!#NrZD!#3?=!#n|$U!#ny-P]PFPO!#3A'D!#3A+L!#3A~!#3AHvQ1R!#3A~!#3A~!#3A~!#3A[!~}$!~[0Q!|o7Q2\!|l~!|l,!{r&c!{r&\C!{sqQ2y!#<6?!{u~!{uxhQ4!#G|~!{u~!{u~!{u~!{u,r!#EzO!{waQ2r!#E,+!{yuu!{y~!{y~!{y918Q28!{y~!{y~!{y~!{y_3s!#nF+0fQ3m+0yS28Q1U'^!#_o+2`PqQ2P!#Pv,1!#nI&P7Q3|I0W!#n7+[003Q!$uR4X-03}H1!$<%&!#_I$!$ug:0GQ2z'@!#_b$1f!#_b&PmQ2HQ3t!#E040V!sZ$sQ!$K^+!s<%1;60an!#_\8!#`2$2bQ2d!#Ea$G}!$8r+!~v%!#^v'fPmB0BQn!#^e$EE!#^dN!$JeY161114Y9SgiPBP8!#Qg+Q0R,4o?FPBPxPpQ0X!#E_%qPoPp!$Jf%014qR!#^e'11^g!#^i$I0ODoD3!#^V-7BQ2i1467S41!#muG`0=!#^J]j!#4@9d!#4=7Q4MQ4L!$J=+!#4F$KP`PGQ29Q!#^D'P!#4K~!#4KHKQ2:Q4X/n9%89RC#NS!s6$P9Q2RQ4X/D9S1KCT[Q4X/s9%`9S1!s\$1K;g9!s<$m9&0M9S2s!s=%5l!s=%q9Q2R#8\CQ4X/r9Q1KQ4X'5\CQ2RP3Q1KP3Q2V/n9Q2:Q2VP9Q2SQ2V!t?,2V/s9Q!t<02V/m9Q!t802V!t8$S!t8$2V!t8&2V!t8%S!t8'!#6}~!#6}~!#6}Q:&0L9$0YQ1CeS4:O1!%;m&9feS1KQ!s9$0YQ0Y;g9!#7T~!$NE003Q3wQ4QQ0D!%23%rQ3!#7n'yQ3o'GQ3nQ28!$#2&y!s%$h'GS287Wa3OI0R3W!$#<2%_sPtPNPoPNP7Q079\NpK!%El$N!#VP+%_tPiPN!sP$tQ2P!#V^$!$M2+4!$]Q$7!%0@$F!#Vm&p!%0@'19!#qH$WQ4560n3Q4pPQQ07!$M/+44!#od$4!sj%G!s=&19P:Q0V!%-?%p/XnS45Q44'@5R!$MW%!se%6#B!#o[$!%Mu&Q2K!sF%203I!$0i'!#q?'0W!%/h$!#:9+4k!$Lt>01!#:9+!t7%!sw%fQ0G!#r^$!$M</4;!%0t$01!sF$!#:<14<Q1;!#r~$47PmQ!$M0$>PmQ4!#rU+257mQ3qQ3v!#:D8PmQ4s>14}!va'2tQ4S#B/@n/@Q:0_m=!$3H$!#:V%EE!$LH%E!$LDWZ0s3Z0t!$LLi%;sS2t/2tP|\CS4s1:96S3v/4u:0Gsi[%;tS3q/2wQ4s14rsQ3v<0Xv[Q46?Jpz@0^hj11p7!#rj$11wY3SPi!$^l&!$L9+0R,4r?FPiQ2mPsQ0X!$LH'PtPrPs!#;}%u14tR!$LZ'Q0}11^wQ4BQ2o!#<$5giQ0tQ4S@0Dpg7<q!#sR&!$K}Q`0s3`0t!$L,iP2Q4SQ4Kf|S1<3F!$'Y<tQ3f#8S4SQ3d#8S2o%8~3S!$'_%!#=5OQ0LQ1KQ1[+08Q4RfsS4R/L91L`9P`Q4RPKP]PJPG!#=[/Q1QQ1<Q4KPxQ0wPwfyfzf{f}p+01CQ4?O_bHc1E!#=iPfc0gc1Nc1Lc19c18c17!s8$6c1Mc1Kc15c14c13!sP$e!#Tas;Q1>!#;g~!#;g~!#Kf~!#Ta\|!#KI&_P1Q3}P7!#uAE=!s2$1I>14nIP!%${?Q4r!#hR&!#t[517!#U_L!#5dW!#hC%B141PP8!%kk>11^7!#tM3!#tF$17!#tFA!#HyZ4V!#tFE`!#tI4!#V:&H!#tG~!}RRg02ZfS4?K0F!s%/c11P>P1P1P?P<P1P1Q0KQ0=!s0%xQ0I!s0$4FPD!s/$2{Q2y!s0%xQ2u!s0%nQ0j!s0$1AQ4X$0VR`!s?%S,4`RGQ4V!s5%kQ1>D~!s$5eQ1HP>P?Q1HP<Q0KQ1HQ0=Q0x!s/$IQ4FQ1HPDQ2{Q1HQ2yQ2!s@$2uQ2n!sI$jQ1AQ1HP`PGQ1HQ4V!t:$JK0N!s%//e1eQ2le!%;e,EeQ1@Q0>Q1F>2=f2P3Q1F-0[2S0>11201[f2RG9z02&0V2R`1?G99z0`7J03YR`'2Z0`3Q2LQ3i-1H^RG7<1Q0;Pg&1:0RDO1PLPDO13A[Q0>P`Ag00GQ0;Pi&1:4RG!sF$G!sF'11141[f1RG,41S0;,L4&0V1S2LP4P4Q2L1?G9'4S3iH0{3YP7P6Pfp,2XCS1EQ1F:023dRGP0p,2WQR`15d0!uE%0<1N1J2;22:f0154dS4O&29fPfQ1EPGP`H27826G20r3GQ04P3&1B3R`?A1GP|[P2&103RD=A`GR<P`PDQ02P3P!%oU$P|n10110_!$PQ$2!$\M$0Z0^`Q4?PGP2J0|P|224|2bDXC<P2O1WC20[12#N20r31R<B02340=A`GB02364=A`GP`P`!t7%`P2P8P2!t6210N10_Z0^`B02386!t9$1DQ1F9A`6P`P3!sd%3P2PBP1!sd@78PGP1J1D157d15BdP215odP3Pd!sv%pRD20[1q!u$%gP|_0Q_0R[Z0N3!sH%oP2PDP`Q1F20[d2#NP|`0Q<_0RZ0_`!wO%dS02#N!s2$r3P31MfdR<Q0a=b@!z:$iQ0c;b1P320hf0g02[BS0421Cf4g02\MS2l&1G1S2kP3&1I0S4VP3&0j4S1AP3&1J6S0jP3&1x8S2nP`&1K8S2uP3&1w7S2xP`%UgP3&0AiP31?2^S2yP321T61S2{!%jx'1!&Tt34F!&Tt,g0qPq!sG20IP3PfPv!&Tl%Q1GP[PwPwQ0XC|P[PxPxg00[jRDH0{%;yS0x?<yDB0}fzdQ0AQ0BQ0CPTPUPVQ0TP[PhPh!sc$Q0`PzQ0_Q0aPhH04Q0S!vD$h20pEhRJQ0f9bOh20TEh14JR%;vS0=AtZvuS0K11uYS2S11ip-0;iS4XP^PpPpP_C|S0wQ2U14oo/5pS0nQ3q@0\tsS4nAFsXRS0^PcPqPqPWC|S1714dqS0m14JtB0oqviPtQ11Q13Q151DuX+0ZI0US4t3J9JJdD3D3Do3Z5ZyK0=D!%4u$hP@1KrBS4rPz20TEjPHPwPvP7M;IfjRJ7dL!sN$jP@1KsoS2BP!uQ$lPHPxPwPBM;IQ297vL!vS8~P~!vS+l!vS&~!vS-~20pE~S2A!vT%~20TE~Q2A/4RQ0xAtZyxS2@11xYS2?!v-&iS3q11^iS2>@0\i_S4m11[gS4lQ4@/5iS4@11wv-0;wS3}AFvXRS2|PcPrPr!vX$4gQ2A14drS4i!t:$wB0orytPw!v]-x!v]'153J7!v\/j!v\$%8qS2A15pyS13Q2M$0ARX7<u1?X^B07zqy,5pS119ZuX5Zq3Y14hv=tcRS1DQ1P,1gS1PP>P?Q2cP@1KxrS4hQ2aQ2e-0TEPHPlPjPiM;IQ1HPd14dvQ1HQ0{Q0{1?v9'4!#9H$S1JPLQ4JH0:Q2tPsPyPl!u`$YC|CuS2tP|_0Z_0?]p_0[]q_0W]b]c_0a_0c_0j_0i_0!&L&/c0}c0zc0xc0vc0wc0yc0|c0uc0{c0~c10c0Vc0mc0lZ1H3Q0a/:<S0a,4@!#39&!s7$c'4!#3>$<Q!#39$<Q2lQ2kP3Q4V!&Lb$3Q0jP3Q2nP`Q2uP3Q!~p%<S2x!~s$<RXP3Q2yP3Q2{PeQ4FP3Q!~8&<!~8,11[<S1GQ0X80\<S0XQ1G1L<DRe'220;<eB0}f<d!sI$!zb3Q0XQ!&fz%a'4S0a,5zPy!z]%'4S0c20pE<RePOP<!#QI$S0f20TE<R<@0XeRS0SQ0=Q0KQ2SQ4XQ!}z$Q0n!#sV%1711edRRQ0m14et'1Q4t!$vm%o!}<0Q4rPzP<!}5-Q4I!}4-Q2BPh!sF$!},'?vLJ!uG=a,5lPjQ0cQ0f!uE$xQ2@Q!|S$Q4mQ!|;$Q3}Q2|Q4gPRQ4i14ew'1Q15!tn0Q2AQ13?<uX1?X^Q!{7-Q!{/$!{%+Q!z}$!tp$!zx,JPLfoS1!z\'3Pd!#??$JQ0;,LJQ2LPJPJQ!#?%%1Mf0>0}f0P|_0X_0H_0YZ0`3Q02Q4I,1dQ4IQ2x7zdQ0{Q4IQ4IQ0{Q2x/?93z3J3YQ1GQ4DP0O1Y0XY0HY0YffS02Q4HQ1KfdS4HfcN91sY0ZY0?WpY0[WqY0WWbWcY0aY0cY0jY0iY!{z[PFp,3CLSS1Dp,2HCp,3HC'S1P!s/$Cp,2CVQ0?Q4AQ3dQ2iQ2NQ2eQ2c!~Z$MNC1rY0QY0RPqP2J1@bDWCPp!s1%CY0dP2O1bC!s+%!s5$P0P1O3WC!s\%Z0_`Z1P3!'0~&O4!%\+$_!%D9'4110`!s7+AA`2GP|[Z0_`PGO1P220k`GO1bCc1=Y0PQ4O#NR`eP`Q051[f6R`9z769J67&0V6R<1?`99z7<7J7Q1=/eBP01[f8R<9zB89J8BQ0@PEPLQ1EQ1FPFPd!yI$0<PKp,2RQS05Q1Pp,4INITS4OQ1DPrPgp,2LOS0?1Mf7R`P7Po!uI$2NH1qY0HP2O1&0V8R@1?<99zB@7J!t8%Q1EPGp,3OKQP`P7P4L1pQ1p%U`R`,47Q1pg01e4'4RG%``3J7J7Q00Q1p/1B1[fBR`,4B%``7JG!uF$qP2!sC$p1[fqR`,4q!sC&001[fgR`=FgG%``!sS$sP21[fr=FrG1[fs#`1MftRG#UR`11`W+0;S1p1h`c11[GR@1MfuR<#URX,1c[&0AGRe11e_+0;&0A<,1^\@1De^+0Z3S!t/$vQ1p1hXc1MfvRX,1[Re1MfwR@#UR<!sk&XRX11X!sk&@,1^\e1DX!sk%Ag@@DS1=%8<#N20`f@,KwRX#;1hX<20hf@$0j9FX<1hw9S2tQ1=1MfxS1G#US4I#8#N1MfyS0{-0`f,Ky#;1MfzRX!s5%z%UXS2x'h1Mfh!s;'h%UXS3i20hfX$0j3FP31Mfj!sE%1Kl21[flS2L'hZ0N3P1&1of21H^cR<7bXR@21nfXJ0|1Kj@%UXS0;'h%82#NRXQ001h0120i04S4h[S2A20i101h40R@[S1120i46\@B1m012S13P!%#[-1!#J<&UZ0J3Z0C3S15Q2A\X`0J3`0C3R@P21Mf~Re=bO<,K~RR%UeS4i!&03/21?bnP:ARmnb-0Pm!#z'2%`2%81!$rs%P2Q2M,[fS4gPgO2bHP1O4Q4i00iRg02]XRRP3!~l$a,Mf!tG%%UeRe,:240GZ0N3Q2a/h9P2Q2eQ2e,MfRV!sL%VS2|!sM%Q15P@P2Q2i,[fR@PcPSPAPNPkQ2\!#ll+!#Y9,%8cRVP|[S3}P2bHPsO420ic@PRP3Q4A,[f1:2cRR'5!tP$4A!tP%4D,[f/5RP3Q09,MfS4@#US4lQ3cQ3c,Mf=bO<1:o!u1'P71:1cRRP2J0|Q09Q4@!sH%BR40GQ00Q2AQ11Q4h1h64[Q13P2!wx7VX!wy'Q11!wv,P2Q2OP9!#^@|21l^cS11%`^S13%;c%`<[!z9&Q1xQ1>B1k^c1UY0HS00!s9%%;<S4@[_0HRX!%`w;8&0L^$0YQ13eS26O1Q4h!w{+19!wp,Q4sP2bHc0r!%Gk1c0rc1F!#Zs>P3Q3f@0~29Z0N31:p4/:ZQ2O,Mf/:YQ3=Q0J#CRR':40D!#coK!#dgK!#d?|PzQ3YO1Q3^?<u!&,T$@O1Q3a?<lW!#xP~1Q2AQ00PX1n]^%8^S00#NP]P^Q1V1D]^RXCT[1s]^Q13AgXX^S2A[1m]^&0M^Al^XX[1q]^Q00Q1V#8[1r!s3$15X][Q4?21u]^R^eP^P6Q!y'$2AP1Q1>Q1xPpP2P1O2Y0CQ1xQ4@_0CPq!sL%4hQ3sQ3m;OaS4hQ0P#C$00R^Q!%I1&Q3k'xS0P3ORX/GX'GS4QQ0Q#CQ3xQ3pQ3k3O/GX+0yS3xQ0E#>P320g3[Q0620g35H1vR561>3-1A3Q3w'GS06Q0F>1>35-1A3S0FQ3rQ3sQ2Q3O'GQ0N!#{h%wQ3h'GQ3zQ3w/GX!s/%!tb$r'xRXQ3m!s3$j'xR53O'G'G3W3WR[5W^3O!%J?$Q4h!uA$xQ!tC$!sV$s'x1^5a5OX'G=W^[!sR'!%Jh$dPAQ3{P6Q3|Pi!#hy$0PNPoQ2PP7Q4Y9\Ni!$nK%P4Q1N9\Ni!sO&!#|>+=97mbP:Q4=Q0:$1961i3R[!s;%!sH%q!#6[&!#|F$8Q4qQ0W!&,F-%BWR^!sL1GP^PIQ0\!&,j,G@0l}[:0n3nQ2\,XQ,X=!%[e/Q1IQ08!tC%ZQ!%[g0PmQ4TQ0G+0!#zT$1f!sG&!%JLR!#{8%057!%JW=!#|A$!#{u/PmQ0]00s!$ol$0\00sbQ43H1{!&,v'Q!%[5/G}I0?I0?P:1X=QQ49Q2X,X}41R%BR80lIQ4p'X9RmnEEEcFjFjFj!%[E~!#{h=!|z%[Q2~P|[PoP_!%Hx%Q3<P|[PqPWPBPrCT[Abq7<1:8c,:660G4PuPPPqQ!$om$Q0M/1gQ0R>0DgPPp!&-p;>!%I;@-08s-08rD3D340^!#nH$UD3H0b1:7B/:Z1:oY1:pR40D>0~89[!%\+~!#{H=2o'2!%H:,!&j'1!#o8A!#o3$AQ2JQ1KQ0tP]POPHPMQ02p+01SRM,MfQ1JfuPMP0Q4H!$9C$p+01[OXbHc0qc0pc1Qb!s:$NRMQ4J/:J/:Z1MfM/:YQ4G/:R40D<0~9ec0e!#oQ/pc0qc1D!%HjFc07c04!#o~13!#o~0c02!#p#/o!#p#+H1gO4bCc0kY1:Z1O3!%G'610`000c0bbCY0kXn!sK@]bCc0]Y0OY0]Y1CY1BY0OPtL1|Q2t!#N\<Q05Q1PQ4OQ1DQ2MPlQ0?Q1GPxPxQ4I/?9PzPuPt!#G/'A7mnn!}J01122^03P2PyO1bHQ4I/n9RyQ2:Q0{#URlP91?l91Dl9CT[RK1sl9RlQ1CQ2x/D9R??g?9[R?Q2x/m9R>Q2sQ3i/D9Rd=l9d[RdQ3i/q9RFQ0;/?9#8\CRLQ0;/r9REQ2L/D9Q2L'5\CRCQ2L/?9RRP3Q4!sj$YP3Q4g/ncRM%NVPePc1?ec1DecCT[RZ1secRe%`cRJQ2c,[fRH/DcRO?gOc[RO1mHcRH&0McQ2|/DcR]=lc][R]Q2|/qcRTQ2N,[fRU/?c#8\VRs1rUcRU1D@c/5@\VRV1?@cR@P3Q3d,[f/DcR~!&H%%c$0YPJeO1RJ!&G|$cRjPrQ4:O1RhQ3[?<o9RoQ1MQ1?Q3h3OQ28!$sg%0PQ3j'^!#;B-PAQ4NQ0O?\4NRN!&z3+1!%\8$QQ2\Q0[P}!#9t'A7mbIQ2=!$7Q-4p/X=RP/@I9R!%\|'}PbP:1@nP1@nQ57m!&>Z$!#7@A1\Q3}P4PcP7P6CT[%;8Rn/2BQ4sQ3v>0X8B[%871:98Q415F6!#|4;P21Lq9P6PqP4Q4lPgQ09PpP1PuPxO;bH!}H$d!#yz-c0V!#y{-P2PyPKPlP?P>PdPFPLPEPCPRP3PYP3PMPZPePOPHP]PTPsPUPVP@P3P~P3PJPjPhP!#B$$!w?$3k;O540fQ3nQ3kQ3j3!%dd$hQ3j3W-0ea!&GR-Q2_?\1N!wP1=Q2\PIPQ!%b4,<Q4p:0_m}!wR05/@}9Rm!wg&PQP!#?e%21?b=P:Q0q!&C/'!wS?!wP%0PcP8P4CT[A<769Q4sP6P9P4P7CT[%88%`8Pn!#9'71\P2Q2T!wG-!wD'Pz!wFIrNN1}c1>Y0OY0bY0OAgGGD%8`20`fG,KtRt1Dt`20hfG$0j9Ft`+08+0;+1~<1Oi-20GJ21Y1AY1@!%Vd?1?!sE=bC!#\@%!%VN/0!%VN'0\c0XO2!#b-$H1eZ0`3P2I22Y1J!#Q8$@eP1K0Fc0Zc0?bpc0[bqc0WbbWcY1Io"). Qed.

  Theorem cache_dealloc_arepq : ltac2:(zQ "70!jmc!jr0!jv2!kj3!ik8!io7!kk4>0>4msF'$4>3mo'$5>0@2$6^2^1@4$2$1$3?1Q@2$0^3^2@4$2$1$3?1Q@2$0?3msF?2mo").
Proof.
  (* LPS revision repair (75d69e00, checker 2c6b6db8).  This proof was a KReplay replay that
     destructured amaps_in_ledger at its PRE-RESTATEMENT shape; its first error was As:148 /
     Bs:149 "Illegal application: and_elimF6" over the old six-conjunct body.  That definition's
     first conjunct is now guarded by a non-zero ledger-word size (As//Bs AllocRep.v, same
     series), so the replay's baked-in motive no longer type-checks.  Written out as plain
     text; the STATEMENT IS UNCHANGED (still the encoded one above).  Text transcribed from
     a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/
     AG_CacheDealloc3.v:176-360, where the same theorem in the same Section is already plain
     text.  It carries NO address of its own: every constant is a symbolic ATP / ATSD /
     AIMG_TOP / AHI_LO / aceil of THIS tree, so nothing is transposed between trees.  The
     restatement costs nothing in this proof: the first conjunct is bound (IL1) and never
     used, and the six-way arity of amaps_in_ledger is unchanged. *)
    intros K. pose proof BND as B. pose proof B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & ECA & EP & ERI & ERB & EFA & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & C1 & V3 & V5 & CNTB & T16 & S16 & P16 & M18).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0). destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    destruct AB0 as [AB0a AB0b].
    (* [comment removed for export] *)
    destruct (cd_cells_of_arepq s m _ _ c RQ HC INIT) as (q0 & q1 & q2 & q3 & PC1 & PC2 & PC3 & PC4 & QST & TST & RIC & RIJ & EXH & RST & FARR & FAJ & USJ & REN).
    fold st TH CA r pc in PC1, PC2, PC3, PC4, QST, TST, RIC, RIJ, EXH, RST, FARR, FAJ, USJ, REN. cbv zeta in PC1.
    change (CA + PCLASS_SIZE * c) with P in PC1, PC2, PC3, PC4. change (a_ri s + REGIONINFO_SIZE * c) with RI in RIC, RIJ, EXH, RST.
    fold cnt chunks mc nf mfa au mu fl in PC1, PC3, PC4, RIC, FARR, FAJ, USJ.
    pose proof (cd_pure s m _ _ c RQ HC INIT) as (_ & _ & U3 & _ & _ & U6 & U7 & U8 & _). fold st r pc in U3, U6, U7, U8. fold nf mfa mu fl cnt chunks in U3, U6, U7, U8.
    eapply (cache_dealloc_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo sb c TH CTX ATSD p cnt mc csz chunks q0 q1 q2 q3 nf mfa au mu fl).
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
    { clear - ERB V3 V5 N8 N9 C1. tlia. }
    { clear - N5. tlia. }
    { exact U8. }
    { exact N4. }
    { fold n. assert (NC : 32 * (nf + cnt) <= 3758096384) by (apply (nc_bound csz nf cnt au mu); clear - B; tlia). unfold kFreeArraySize. clear - N1 N2 N3 N4 N5 N6 N7 NC. tlia. }
    { constructor. unfold kFreeArrayMapSize. exact M18. }
    { unfold kUserMapSize, kFreeArrayOffset. clear - N8 N9. tlia. }
    { exact U7. }
    { exact OK. }
    { exact VISE. }
    { exact MI. }
    { exact ST. }
    { replace tp with (wz ATP); [exact REN| unfold wz; rewrite <- TP; apply Z_to_bv_bv_unsigned]. }
    { exact PC1. }
    { exact PC2. }
    { exact PC3. }
    { exact PC4. }
    { exact QST. }
    { exact TST. }
    all: try replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI by (unfold kSpaceSize, REGIONINFO_SIZE; clear - ERI; tlia).
    all: try replace (sb + c * 2 ^ 32) with (RB s c) by (clear - ERB; tlia).
    all: try replace (RB s c + kFreeArrayOffset) with (FA s c) by (unfold kFreeArrayOffset; clear - EFA; tlia).
    { exact RIC. }
    { exact RST. }
    { exact FARR. }
    { exact FAJ. }
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
    destruct POST as (OK2 & VIS2 & LED & MU & WM & MI2 & REN2 & ST2 & PC1' & PC3' & PC4' & QST' & TST' & RI' & RST' & FARR' & FAJ' & POI').
    destruct LED as (EL & ES & NVS & VMM & VMR & VML & VMB & VBRK & VMN & EAG).
    rewrite Z.ltb_irrefl in EL, ES, VMN. rewrite Z.sub_diag, Z.add_0_r in EAG. rewrite app_nil_l in ES || idtac. cbn [app] in ES.
    (* [comment removed for export] *)
    change (cnt =? mc) with drained in EL, ES, VMN, EAG, MU, PC1', PC3', PC4', RI', FARR', FAJ', POI'.
    change (mc / 2) with n in EL, ES, VMN, EAG, MU, PC1', PC3', PC4', RI', FARR', FAJ', POI'.
    change (if drained then rta_mfa nf n mfa else mfa) with mfa' in EL, ES, VMN, EAG, MU, RI', FAJ', POI'.
    change (if drained then n else 0) with k in MU, PC1', PC3', PC4', RI', FARR', FAJ'.
    replace (sb + c * 2 ^ 32 + kFreeArrayOffset) with (FA s c) in EL, ES, VMN, MU, FARR', FAJ', POI' by (unfold kFreeArrayOffset; clear - ERB EFA; tlia).
    replace (sb + c * 2 ^ 32) with (RB s c) in PC3' by (clear - ERB; tlia).
    replace (sb + kSpaceSize + REGIONINFO_SIZE * c) with RI in MU, RI', RST' by (unfold kSpaceSize, REGIONINFO_SIZE; clear - ERI; tlia).
    change (TH + 208 + PCLASS_SIZE * c) with P in MU, PC1', PC3', PC4'. change (TH + 208) with CA in MU.
    change (Z.shiftr (p - RB s c) kCompactPtrScale) with (addr_to_compact st c p) in PC3'.
    (* [comment removed for export] *)
    assert (DR : if drained then cnt = mc else cnt < mc).
    { unfold drained. destruct (Z.eq_dec cnt mc) as [E|NE]; [rewrite (proj2 (Z.eqb_eq _ _) E); exact E| rewrite (proj2 (Z.eqb_neq _ _) NE); clear - NE N4; tlia]. }
    assert (NC : 32 * (nf + cnt) <= 3758096384) by (apply (nc_bound csz nf cnt au mu); clear - B; tlia).
    assert (FROOM0 : efs_new (nf + n) <= kFreeArraySize).
    { unfold efs_new, round_up, kFreeArrayMapSize, kFreeArraySize. clear - B NC. Z.div_mod_to_equations. tlia. }
    pose proof (cd_state_fields st XC XB c p drained WQ HC' INIT CLS DR FROOM0) as FLD. cbv zeta in FLD.
    fold pc r cnt chunks nf mfa au mu fl mc n k in FLD. change (if drained then rta_mfa nf n mfa else mfa) with mfa' in FLD. fold st' in FLD.
    change (free_array_base st c) with (FA s c) in FLD.
    destruct FLD as (Fpc_c & Fpc_o & Frg_c & Frg_o & Fmaps & Fsb & Fpa & Fsec & Fch & Ftq & Fgq & Fnr & Fci & Fii & Fqx & Fqn & Fqc).
    pose proof (WFQ_cd_state st XC XB c p drained WQ HC' INIT CLS DR FROOM0) as WQ'. fold st' in WQ'.
    set (sA := mkAst st' TH CTX (a_fsb s) L' S' (a_Zr s) (a_AL s) (a_top s) (a_bot s)).
    destruct (cd_zones m' MU) as (AGsp & AGpend & AG2).
    pose proof (kr_of_flag drained cnt mc n nf mfa k mfa' eq_refl eq_refl eq_refl DR) as KR.
    pose proof (froom_of_flag drained n nf mfa mfa' eq_refl ltac:(unfold kFreeArraySize; exact N3) FROOM0) as FROOM.
    (* [comment removed for export] *)
    pose proof (munch_agree _ _ _ MU) as AGW.
    assert (JK2 : junk m' p csz).
    { eapply (junk_transport_pt (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa')) m m' AGW WM); [exact SLOTJ|].
      intros a Ha. apply (ZC_slotW s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO). left. exact Ha. }
    assert (PS2 : poisoned m' p (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic).
    { eapply (poisoned_transport_pt (outside (lcd_W lo (bv_unsigned sp) P CA (cnt - k) RI (FA s c) TH nf mfa mfa')) m m' AGW WM); [exact SLOTP|].
      intros a Ha. apply (ZC_slotW s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO). right.
      rewrite Z2Nat.id in Ha by (clear - C1; Z.div_mod_to_equations; tlia). exact Ha. }
    (* [comment removed for export] *)
    assert (R2 : AREPQ sA XC XB m').
    { eapply (arepq_after_cd s m m' XC XB c p st' L' S' (a_AL s) lo (bv_unsigned sp) q0 q1 q2' q3 k mfa');
        first [exact RQ| exact HC'| exact INIT| exact CLS| exact KR| exact FROOM| exact WQ'| exact LO| exact AG2| exact WM| exact JK2| exact PS2| eassumption| idtac]. all: fail "R2". }
    assert (AWV2 : awin_vis sA m').
    { exact (awin_after_cd s m m' XC XB c p st' L' S' (a_AL s) lo k mfa' RQ HC' INIT CLS KR FROOM ES LO WM POI' AWV). }
    assert (FX2 : flagsx_rep m').
    { exact (flagsx_after_cd s m m' XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO AG2 WM FXR). }
    assert (AMX2 : AMODELX sA mo2).
    { eapply (amodelx_after_cd s mo mo2 XC (p :: XB) c st' L' S' (a_AL s) k mfa' (firstn (Z.to_nat k) chunks ++ fl));
        first [exact AMX| exact PL| exact WQ| exact HC| idtac].
      all: try first [exact FROOM| exact Fsb| exact Fpa| exact Fsec| exact Frg_c| exact Frg_o| exact Fmaps| exact EL| exact ES| exact VMM| exact VMR| exact VML| exact VMB| exact VMN| exact EAG].
      - destruct KR as [(K0 & M0 & _)|(Kn & _ & Mn)]; [left; exact (conj K0 M0)| right; exact (conj Kn Mn)].
      - exact (lazy_ranges_okb_nowrap asegs _ (lzok_ranges OK)).
      - exact (nonvm_same_atop _ _ NVS).
      - clear - AB0a. tlia. }
    (* [comment removed for export] *)
    assert (DEP2 : DEPOT asegs d m').
    { eapply (DEPOT_transport asegs d m m' _ DEP MU WM).
      pose proof (depot_avoid_cd s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO d DPL) as DAV.
      unfold depot_avoid, avoids in DAV |- *. rewrite !Forall_app in DAV. clear - DAV. tauto. }
    (* [comment removed for export] *)
    assert (MODEL : forall stA, same_but_shadow stA st -> exists stA' ev, cache_dealloc stA c p = Some (stA', ev) /\ same_but_shadow stA' st').
    { intros stA SBS. apply (cd_state_eval st XC XB c p drained WQ HC' INIT DR FROOM0 stA SBS).
      intros DT GT.
      assert (IM : forall a, sb <= a -> a + 1 <= aceil -> addr_is_in_mem a = true).
      { intros a Ha Hb. apply in_mem_high. unfold kHighMemBeg, kHighMemEnd. acb. clear - Ha Hb B ACEILB. tlia. }
      change (free_array_base st c) with (FA s c). fold r in GT |- *. fold nf mfa mc in GT |- *. fold n in GT |- *.
      assert (E1 : efs_new (nf + n) = mfa + 262144).
      { unfold efs_new, round_up, kFreeArrayMapSize. clear - B GT NC. Z.div_mod_to_equations. tlia. }
      rewrite E1. split; [| split; [| split]].
      - change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - B; tlia). change (2 ^ 3) with 8. clear - B M18. Z.div_mod_to_equations. tlia.
      - apply IM; clear - B; tlia.
      - change 7 with (Z.ones 3). rewrite Z.land_ones by (clear - B; tlia). change (2 ^ 3) with 8. clear - B M18. Z.div_mod_to_equations. tlia.
      - apply IM; clear - B; tlia. }
    (* [comment removed for export] *)
    assert (KB2 : 0 <= k <= cnt /\ mfa <= mfa' <= 536870912).
    { unfold kFreeArraySize in FROOM. revert FROOM. pose proof KR as KR'. fold mc in KR'. fold n in KR'. destruct KR' as [(-> & -> & _)|(-> & E & ->)]; [clear - B; intros; tlia|].
      unfold rta_mfa, efs_new, round_up, kFreeArrayMapSize. destruct (Z.leb_spec (4 * (nf + n)) mfa) as [LE|GT]; [clear - B E; intros; tlia|]. clear - B E GT. intros FROOM. Z.div_mod_to_equations; tlia. }
    assert (SB2 : sh sb <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh (sb + 2 ^ 37 + 4096)).
    { unfold sh. change (2 ^ 37) with 137438953472. clear - B KB2. Z.div_mod_to_equations. tlia. }
    apply K. unfold cd_gpost, rstep_post.
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
      unfold lcd_W in Hiv. unfold awrit. change (a_thr s) with TH. change (a_sb s) with sb.
      destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Ha; unfold kPageSize, kSpaceSize;
        first [ left; exact Ha
              | right; left; clear - Ha B KB2; tlia
              | right; right; left; clear - Ha B KB2; tlia
              | right; right; right; left; clear - Ha B KB2 SB2; tlia ].
    - apply avis_of_wmono. exact WM.
    - exact AGpend.
    - (* [comment removed for export] *)
      intros ch0 H0 _. cbn [a_st]. unfold chunk_list. rewrite Fch. exact H0.
    - (* [comment removed for export] *)
      intros a (ch0 & H0 & E0 & Ha). apply AG2.
      pose proof (record_extQ s _ _ OKQ ch0 H0) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). pose proof (chunk_alignQ s _ _ OKQ ch0 H0) as (_ & _ & A3 & _).
      assert (RU : ch_used ch0 <= round_up (ch_used ch0) 8 /\ 0 <= nsh (ch_used ch0) /\ 8 * nsh (ch_used ch0) = round_up (ch_used ch0) 8)
        by (clear - X9; unfold nsh, round_up; Z.div_mod_to_equations; tlia).
      destruct Ha as [Ha|Ha].
      + apply (ZC_rec s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO ch0 a H0). clear - Ha X3 X6 X7 X8 RU. tlia.
      + apply (ZC_rec_sh s m XC XB c p lo (bv_unsigned sp) k mfa' RQ HC' INIT CLS KR FROOM LO ch0 (ch_user_beg ch0) (nsh (ch_used ch0)) a H0);
          [clear - X3 X6 X8; tlia| clear - X7 RU; tlia| clear - A3; Z.div_mod_to_equations; tlia| clear - RU; tlia| exact Ha].
    - exact MODEL.
  Qed.


End CDStep.
End HCW.
